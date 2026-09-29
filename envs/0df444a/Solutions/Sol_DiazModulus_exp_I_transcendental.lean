-- Prove2me | solution 1 for DiazModulus.exp_I_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T06:21:45.653434+00:00
-- url     : https://prove2.me/submissions/d191bb3f-c9a5-43e3-acaa-c66fd4299d21

import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

private theorem I_alg : IsAlgebraic ℚ Complex.I := by
  refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
  · intro h
    have := congrArg (Polynomial.coeff · 0) h
    simp at this
  · simp [Polynomial.aeval_def, Complex.I_sq]

open DiazModulus in
theorem solution : Transcendental ℚ (Complex.exp Complex.I) :=
  hermite_lindemann_holds Complex.I Complex.I_ne_zero I_alg
