import computability.turing_machine
import computability.tm_computable
import tactic
import data.fintype.basic
import data.fintype.card
import data.pi
import data.nat.pow
import data.nat.log

open_locale big_operators

-- set_option pp.implicit true

/-
  This file contains theorems about Turing machines (in the TM2 model) with space restrictions
  
  # Definitions
    * `bounded_stacks` A finite type consisting of |K| stacks, each of at most size M
    * `bounded_cfg` A finite type representing a configuration whose stacks are bounded by M
                      (i.e. using `bounded_stacks`)
    * `bounded_cfg' M c` Given M : ℕ and c : cfg, does c take up O(M) space
      (more preciesely, it simply checks if every stack has at most M elements)
    * `bounded_cfg_to_cfg` a bijection between the finite type `bounded_cfg` 
                            and cfg's satisfying `bounded_cfg'`
  
  # Theorems
    * `bounded_stacks_size` Given M, gives an upper bound
                            for the number of possible configurations of `bounded_stacks M`
    * `cfg_space_upper_bound_finitely_many` Gives an upper bound of the form O(2^(O(M)))
                            for the number of possible configurations satisfying bounded_cfg'.
-/



/-
  Here we just list some useful generic lemmas that are used in the file
-/

-- A wrapper for multiset.sum_le_card_nsmul for finite types instead of sets
-- (Simplifying `map` each time is a little annoying)
lemma sum_bound {α : Type} [fintype α] (f : α → ℕ) (b : ℕ) (f_bound: ∀a : α, f a ≤ b) 
  : ∑ a : α, f a ≤ (fintype.card α) * b := begin
    have : ∑ a : α, f a = (multiset.map f finset.univ.val).sum := by refl,
    rw this,
    have : fintype.card α = (multiset.map f finset.univ.val).card := by {
      rw multiset.card_map f finset.univ.val, refl,
    },
    rw this,
    apply multiset.sum_le_card_nsmul,
    finish,
end

-- A wrapper for multiset.prod_le_of_forall_le for finite types instead of sets
lemma prod_bound {α : Type*} [fintype α] (f : α → ℕ) (b : ℕ) (f_bound: ∀a : α, f a ≤ b) 
  : ∏ a : α, f a ≤ b ^ (fintype.card α) := begin
    have : ∏ a : α, f a  = (multiset.map f finset.univ.val).prod := by refl,
    rw this,
    have : fintype.card α = (multiset.map f finset.univ.val).card := by {
      rw (multiset.card_map f finset.univ.val), refl, 
    },
    rw this,
    apply multiset.prod_le_of_forall_le,
    finish,
end

-- A little bit annoying since 0^0 > 0^1, so pow isn't monotonic; this abstracts away the casework
lemma pow_le_pow_plus_one { a b c d : ℕ } (a_le_b : a ≤ b) (c_le_d : c ≤ d) : (a^c ≤ b^d + 1) :=
begin
  have h : a^c ≤ b^c := nat.pow_le_pow_of_le_left a_le_b c,
  have h' : b^c ≤ b^d + 1 := begin
    cases b with b',
    {
      exact calc 0^c ≤ 1 : by { rw zero_pow_eq, split_ifs, repeat { simp }, }
                ...  ≤ 0^d + 1 : by { simp },
    },
    {
      exact calc b'.succ^c ≤ b'.succ^d : by { apply nat.pow_le_pow_of_le_right, simp, assumption, }
                      ...  ≤ b'.succ^d + 1 : by { simp },
    },
  end,
  exact le_trans h h',
end


lemma vector.heq {α : Type*} {m n : ℕ} {v1 : vector α m} {v2 : vector α n}
  (leq : v1.to_list = v2.to_list) (H : m = n) : v1 == v2 :=
begin
  subst H,
  rw heq_iff_eq,
  exact vector.eq v1 v2 leq,
end

section prelim_definitions

/-
  In this section, we fix a language for our TM2, i.e.
  a fixed index set for the stacks K, type of stack elements Γ, type of function labels Λ
  and variables σ
-/
parameters {K : Type*} [decidable_eq K] [fintype K]
parameters (Γ : K → Type*) [Π k, fintype (Γ k)] -- Type of stack elements
parameters (Λ : Type*) [fintype Λ] -- Type of function labels
parameters (σ : Type*) [fintype σ] -- Type of variable settings

open turing

def cfg := @TM2.cfg K _ Γ Λ σ
-- Aliases for all the methods of `cfg`
def cfg.l := @TM2.cfg.l
def cfg.var := @TM2.cfg.var
def cfg.stk : cfg → ∀ k : K, list (Γ k) := TM2.cfg.stk
def cfg.mk := @TM2.cfg.mk
def cfg.mk.inj := @TM2.cfg.mk.inj

@[reducible] def stacks := Π k : K, list (Γ k)

-- Extensionality for TM2 configurations
-- There should definitely be a better way to do this
theorem cfg_eq : ∀(c1 c2 : cfg), (cfg.l c1 = cfg.l c2) → (cfg.var c1 = cfg.var c2)
   → (cfg.stk c1 = cfg.stk c2) → c1 = c2
  | ⟨l, var, stk⟩ ⟨l', var', stk'⟩ rf rf' rf'' :=
  begin
    have l_eq : l = l' := by exact rf,
    rw l_eq,
    have var_eq : var = var' := by exact rf',
    rw var_eq,
    have stk_eq : stk = stk' := by exact rf'',
    rw stk_eq,
  end

section bounded_space
/-
  Fix an upper bound M for the maximum stack size of any stack.
-/
parameters (M : ℕ) -- max stack size


-- These `reducible`s are necessary to get infer_instance to work
@[reducible] def bounded_stacks : Type* := Π k : K, Σ n : fin M, vector (Γ k) n

@[reducible] def bounded_cfg := (option Λ) × σ × bounded_stacks

-- The proposition that c : cfg is bounded by M
@[reducible] def bounded_cfg' (c : cfg) := ∀k : K, (cfg.stk c k).length < M



/-
  Converts a bounded_stacks type to the ordinary stacks type
-/
def bounded_stacks_to_stacks (b_stk : bounded_stacks) : stacks := λk : K, (b_stk k).2.to_list

lemma bounded_stacks_to_stacks_preserves_bound (b_stk : bounded_stacks) 
  : (∀k : K, list.length (bounded_stacks_to_stacks b_stk k) < M) :=
begin
  intro k,
  -- Unfold the definition
  suffices : ((vector.to_list (b_stk k).2).length < M), { exact this, },
  rw vector.to_list_length (b_stk k).2,
  exact fin.is_lt (b_stk k).1,
end

lemma bounded_stacks_to_stacks.inj : function.injective bounded_stacks_to_stacks :=
begin
  intros x y h,
  apply funext,
  intro k,
  have eq_snd_lst : (x k).2.to_list = (y k).2.to_list :=
  begin
    apply @congr_fun _ _ (bounded_stacks_to_stacks x) (bounded_stacks_to_stacks y),
    assumption,
  end,
  have x_k_eq_y_k_fst : ↑(x k).1 = ↑(y k).1 := 
  begin
    have eq_len : (x k).2.to_list.length = (y k).2.to_list.length := by rw eq_snd_lst,
    repeat {rw vector.to_list_length at eq_len},
    assumption,
  end,
  have x_k_eq_y_k_snd : (x k).2 == (y k).2 := vector.heq eq_snd_lst x_k_eq_y_k_fst,
  exact sigma.ext (fin.ext x_k_eq_y_k_fst) x_k_eq_y_k_snd,
end

lemma bounded_stacks_to_stacks.sur (stk : stacks) (bound : ∀k : K, (stk k).length < M)
  : (∃b : bounded_stacks, bounded_stacks_to_stacks b = stk) :=
begin
  use λ k : K, ⟨
    (⟨(stk k).length, bound k⟩ : fin M),
    (⟨stk k, rfl⟩ : vector (Γ k) (stk k).length)
  ⟩,
  refl,
end


/-
  Converts a bounded_cfg type to the ordinary cfg type
-/
def bounded_cfg_to_cfg (bc : bounded_cfg) := cfg.mk bc.1 bc.2.1 (bounded_stacks_to_stacks bc.2.2)
lemma bounded_cfg_to_cfg_preserves_bound (bc : bounded_cfg)
  : (bounded_cfg' (bounded_cfg_to_cfg bc)) := 
begin
  intro k,
  have : bounded_cfg_to_cfg bc = cfg.mk bc.1 bc.2.1 (bounded_stacks_to_stacks bc.2.2) := by refl,
  rw this,
  have : (∀l : (option Λ), ∀v : σ, ∀stk : stacks, cfg.stk (cfg.mk l v stk) = stk) := 
    by { intros, refl, },
  rw this,
  apply bounded_stacks_to_stacks_preserves_bound,
end

lemma bounded_cfg_to_cfg.inj : function.injective bounded_cfg_to_cfg :=
begin
  intros x y h,
  suffices : x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2 = y.2.2,
  repeat { apply prod.ext },
  repeat { tauto },
  have h' := cfg.mk.inj h,
  repeat { split },
  repeat { tauto },
  apply bounded_stacks_to_stacks.inj,
  tauto,
end

lemma bounded_cfgs_to_cfgs.sur (c : cfg) (bound : bounded_cfg' c)
 : ∃c' : bounded_cfg, (bounded_cfg_to_cfg c') = c :=
begin
  cases (bounded_stacks_to_stacks.sur (cfg.stk c) bound) with bstk bstk_h,
  use (cfg.l c, cfg.var c, bstk),
  have : bounded_cfg_to_cfg (cfg.l c, cfg.var c, bstk)
       = cfg.mk (cfg.l c) (cfg.var c) (bounded_stacks_to_stacks bstk) := by refl,
  rw bstk_h at this,
  rw this,
  apply cfg_eq,
  repeat {refl},
end

-- The maximum alphabet size
def max_alphabet_size : ℕ := (finset.fold max 0 (λ k : K, fintype.card (Γ k)) (@finset.univ K _))

lemma max_alphabet_max : ∀k : K, fintype.card (Γ k) ≤ max_alphabet_size :=
begin
  intro k,
  have : (max_alphabet_size = (finset.fold max 0 (λ k : K, fintype.card (Γ k))
      (@finset.univ K _))) := by refl,
  rw this,
  rw finset.le_fold_max,
  right,
  use k,
  split,
  { exact finset.mem_univ k },
  { exact rfl.ge },
end

def num_tapes : ℕ := fintype.card K

def C : ℕ := 2 * num_tapes * nat.clog 2 (max_alphabet_size + 2)
def K_val : ℕ := 2^num_tapes

-- Give an upper bound on the number of bounded stacks
-- of the form O(2^O(M)) (notice `C` and `K_val` don't depend on `M`)
theorem bounded_stacks_size : fintype.card bounded_stacks ≤ K_val * 2^(C*M) :=
begin
  simp,

  -- Get an upper bound for the thing inside the sum
  have ub : ∀ k : K, ∀ m : fin M, (fintype.card (Γ k)) ^ ↑m ≤ max_alphabet_size ^ M + 1 :=
  begin
    intros k m,
    apply pow_le_pow_plus_one,
    { exact max_alphabet_max k, },
    { exact le_of_lt (fin.is_lt m), },
  end,

  -- Upper bound of the sum
  have ub_sum : ∀ k : K, (∑ (m : fin M), (fintype.card (Γ k))^(↑m : ℕ) 
                            ≤ M * (max_alphabet_size ^ M + 1)) :=
  begin
    intro k,
    have M_eq_n_lt_M : M = fintype.card (fin M) := (fintype.card_fin M).symm,
    have h := sum_bound (λ m : fin M, (fintype.card (Γ k))^(↑m : ℕ)) (max_alphabet_size ^ M + 1) _,
    {
      rw ← M_eq_n_lt_M at h,
      exact h,
    },
    exact ub k,
  end,

  -- More useful upper bound for the sum
  have ub_sum' : ∀ k : K, (∑ (m : fin M), (fintype.card (Γ k))^(↑m : ℕ) ≤ 
                            2 * (max_alphabet_size + 2) ^ (2*M)) :=
  begin
    intro k,
    exact calc (∑ (m : fin M), (fintype.card (Γ k))^(↑m : ℕ))
        ≤ M * (max_alphabet_size^M + 1) : ub_sum k
    ... = M * max_alphabet_size^M + M : by { rw left_distrib _ _ _, simp, }
    ... ≤ M * (max_alphabet_size + 2)^M + M : by { simp, apply mul_le_mul_left',
                                                  apply nat.pow_le_pow_of_le_left, simp, }
    ... ≤ 2^M * (max_alphabet_size + 2)^M + M : by { simp, exact le_of_lt (nat.lt_two_pow M), }
    ... ≤ (max_alphabet_size + 2)^M * (max_alphabet_size + 2)^M + M : by { 
                                            simp, apply nat.pow_le_pow_of_le_left, simp, }
    ... = (max_alphabet_size + 2)^(2 * M) + M : by { ring_exp, }
    ... ≤ (max_alphabet_size + 2)^(2*M) + 2^M : by { simp, exact le_of_lt (nat.lt_two_pow M), }
    ... ≤ (max_alphabet_size + 2)^(2*M) + (2^M)^2 : by { simp, nlinarith, }
    ... = (max_alphabet_size + 2)^(2*M) + 2^(2*M) : by { ring_exp, }
    ... ≤ (max_alphabet_size + 2)^(2*M) + (max_alphabet_size + 2)^(2*M) : by { 
                                            simp, apply nat.pow_le_pow_of_le_left, simp, }
    ... = 2 * (max_alphabet_size + 2)^(2*M) : by { ring, },
  end,

  -- Upper bound of product
  exact calc 
      ∏ k : K, ∑ (m : fin M), (fintype.card (Γ k))^(↑m : ℕ) 
        ≤ (2 * (max_alphabet_size + 2) ^ (2*M))^num_tapes : by { apply prod_bound, exact ub_sum',}
    ... = 2^num_tapes * (max_alphabet_size + 2) ^ (2 * M * num_tapes) : by { rw mul_pow, simp, 
                                                                            left, rw ← pow_mul, }
    ... ≤ 2^num_tapes * (2^(nat.clog 2 (max_alphabet_size + 2))) ^ (2 * M * num_tapes) : by {
      simp, apply nat.pow_le_pow_of_le_left,
      have : 1 < 2 := by simp,
      rw nat.le_pow_iff_clog_le this, 
    }
    ... = 2^num_tapes * 2^(2 * num_tapes * nat.clog 2 (max_alphabet_size + 2) * M) : by ring_exp
    ... = K_val * 2^(C * M) : by refl,
end

-- Bounded (standard) cfgs, which are isomorphic to bounded_cfg, except
-- that the latter is a finite type
def all_bounded_cfgs : finset cfg := 
      finset.map ⟨bounded_cfg_to_cfg, bounded_cfg_to_cfg.inj⟩ finset.univ

lemma all_bounded_configs_iff_bounded : ∀c : cfg, c ∈ all_bounded_cfgs ↔ bounded_cfg' c :=
begin
  have all_bounded_cfgs_def 
    : all_bounded_cfgs = finset.map ⟨bounded_cfg_to_cfg, bounded_cfg_to_cfg.inj⟩ finset.univ := rfl,
  rw all_bounded_cfgs_def,
  intro c,
  split,
  {
    simp,
    intros l var stk h_bounded,
    rw ← h_bounded,
    exact bounded_cfg_to_cfg_preserves_bound (l, var, stk),
  },
  {
    intro h_bounded,
    simp,
    have b_exists := bounded_cfgs_to_cfgs.sur c h_bounded,
    cases b_exists with bc bch,
    use bc.1, use bc.2.1, use bc.2.2,
    exact bch,
  },
end

lemma all_bounded_cfgs_size_eq_bounded_cfgs : all_bounded_cfgs.card = fintype.card bounded_cfg :=
begin
  have all_bounded_cfgs_def 
    : all_bounded_cfgs = finset.map ⟨bounded_cfg_to_cfg, bounded_cfg_to_cfg.inj⟩ finset.univ := rfl,
  rw all_bounded_cfgs_def,
  simp only [finset.card_map],
  refl,
end

end bounded_space

/-
Given an upper bound M on the space of a configuartion,
it must be one of finitely many configurations, which we collect in f.
There are only O(2^O(M)) such possible configurations, so |f| <= O(2^O(M))
-/
theorem cfg_space_upper_bound_finitely_many : ∃ C K_val : ℕ, ∀M : ℕ, 
    (all_bounded_cfgs M).card ≤ K_val * 2^(C * M):=
begin
  use C,
  use (fintype.card (option Λ)) * (fintype.card σ) * K_val,
  intro M,
  rw all_bounded_cfgs_size_eq_bounded_cfgs M,
  repeat {rw fintype.card_prod},
  rw fintype.card_option,
  exact calc
    (fintype.card Λ + 1) * (fintype.card σ * fintype.card (bounded_stacks M))
      =  (fintype.card Λ + 1) * (fintype.card σ * fintype.card (bounded_stacks M)) : by ring
  ... ≤ (fintype.card Λ + 1) * (fintype.card σ * (K_val * 2 ^ (C * M))) :
    nat.mul_le_mul_left (fintype.card Λ + 1) (nat.mul_le_mul_left (fintype.card σ) (bounded_stacks_size M))
  ... = (fintype.card Λ + 1) * fintype.card σ * K_val * 2 ^ (C * M) : by ring,
end

end prelim_definitions

-- TM2 with finite alphabet
structure fin_tm2' extends turing.fin_tm2 :=
  [Γ_fin: ∀k : K, fintype (Γ k)]
 
#check @turing.TM2.cfg.mk

section tm_definitions
parameter (tm : fin_tm2')

def cfg' := @turing.TM2.cfg tm.K _ tm.Γ tm.Λ tm.σ
def cfg'.mk := @turing.TM2.cfg.mk tm.K _ tm.Γ tm.Λ tm.σ

def option_cfg_bounded (M : ℕ) :  option cfg' → Prop
  | none      := true
  | (some c') := @bounded_cfg' tm.K tm.K_decidable_eq tm.K_fin tm.Γ
                             tm.Γ_fin tm.Λ tm.Λ_fin tm.σ tm.σ_fin M c'

structure evals_to_in_space (f : cfg' → option cfg') (a : cfg') (b : option cfg') (m : ℕ)
  extends turing.evals_to f a b :=
  (bounded_memory : ∀n ≤ [steps], (option_cfg_bounded m ((flip bind f)^[steps] a))) 


-- TODO: evals_to_in_space M --> evals_to_in_time O(2^O(M))
-- (hence we can prove L ⊆ P and PSPACE ⊆ EXP)

-- TODO: evals_to_in_time M --> evals_to_in_space M
-- (hence P ⊆ PSPACE)

end tm_definitions

