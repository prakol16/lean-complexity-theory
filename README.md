# Lean Complexity Theory

My experiments with the theorem prover Lean. So far we just have a proof of the fact that a Turing machine constrained to memory `M` has a number of configurations bounded by `O(2^O(M))`.

In the future, if I have time, I may expand this to a prove that `PSPACE` is contained in `EXPTIME`, that `L` is contained in `P` (although `L` is a bit harder
to define, since it needs a special way to read input and write output), and that `P` is contained in `PSPACE`.
