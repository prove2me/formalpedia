-- Prove2me | solution 1 for DiazModulus.log_two_diaz_or_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:37:37.320345+00:00
-- url     : https://prove2.me/submissions/f478cd60-0ce5-4d21-89c1-082e893fb233

import Mathlib
import Theorems.Thm_DiazModulus_diaz_number_forces_transcendence

/-- Suppose both numbers are algebraic. Then `ρ = log² 2 + π²` is algebraic (it is the square
of the first number), and `e^{log 2} = 2` is algebraic, so part (a) of
`DiazModulus.diaz_number_forces_transcendence` at `t = log 2` makes `e^{i log² 2 / π}`
transcendental, a contradiction. -/
theorem solution :
    Transcendental ℚ (Real.sqrt (Real.log 2 ^ 2 + Real.pi ^ 2)) ∨
      Transcendental ℚ (Complex.exp (Complex.I * ((Real.log 2 : ℝ) : ℂ) ^ 2 / ((Real.pi : ℝ) : ℂ))) := by
  by_contra h
  simp only [not_or, Transcendental, not_not] at h
  obtain ⟨hs, he⟩ := h
  -- `ρ = log² 2 + π²` is algebraic, as a real number and then as a complex number
  have hρR : IsAlgebraic ℚ (Real.log 2 ^ 2 + Real.pi ^ 2) := by
    have h2 := hs.pow 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hρ : IsAlgebraic ℚ (((Real.log 2 ^ 2 + Real.pi ^ 2 : ℝ)) : ℂ) :=
    hρR.algebraMap (A := ℂ)
  -- `log 2 ≠ 0` and `e^{log 2} = 2`
  have ht : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hexp : IsAlgebraic ℚ (Complex.exp ((Real.log 2 : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (2 : ℚ)
  exact (DiazModulus.diaz_number_forces_transcendence (Real.log 2) ht hexp hρ).1 he

#print axioms solution
