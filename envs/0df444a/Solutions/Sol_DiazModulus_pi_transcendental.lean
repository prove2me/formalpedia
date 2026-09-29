-- Prove2me | solution 1 for DiazModulus.pi_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T04:28:52.262126+00:00
-- url     : https://prove2.me/submissions/8da195d8-3e59-4617-b113-0e454d7cb155

import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate


private theorem I_alg : IsAlgebraic ℚ Complex.I := by
  refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
  · intro h
    have := congrArg (Polynomial.coeff · 0) h
    simp at this
  · simp [Polynomial.aeval_def, Complex.I_sq]

open DiazModulus in
theorem solution : Transcendental ℚ ((Real.pi : ℝ) : ℂ) := by
  intro halg
  have hIpi : IsAlgebraic ℚ (Complex.I * ((Real.pi : ℝ) : ℂ)) := I_alg.mul halg
  have hne : Complex.I * ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have hT := hermite_lindemann_holds _ hne hIpi
  apply hT
  rw [show Complex.I * ((Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) * Complex.I by ring,
    Complex.exp_mul_I]
  simp [Real.cos_pi, Real.sin_pi]
  exact (isAlgebraic_one).neg
