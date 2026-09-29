-- Prove2me | solution 1 for Diaz.normalization_not_invariant
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:07:10.24799+00:00
-- url     : https://prove2.me/submissions/3b963972-eb2d-4bd4-a22b-83a82da30d2b

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

open Diaz in
theorem solution
    (HL : ∀ z : ℂ, z ≠ 0 → IsAlgebraic ℚ z → Transcendental ℚ (Complex.exp z)) :
    ∃ u : ℂ, u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp u) ∧
      Transcendental ℚ (Complex.exp ((((‖u‖ : ℝ) : ℂ))⁻¹ * u)) := by
  have hI : IsAlgebraic ℚ Complex.I := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.coeff · 0) h
      simp at this
    · simp [Polynomial.aeval_def, Complex.I_sq]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨2 * (Real.pi : ℂ) * Complex.I, ?_, ?_, ?_⟩
  · simp [Complex.I_ne_zero, Real.pi_ne_zero]
  · rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
  · have hnorm : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [hnorm]
    have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpi
    have e : (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (2 * (Real.pi : ℂ) * Complex.I) = Complex.I := by
      push_cast
      field_simp
    rw [e]
    exact HL Complex.I Complex.I_ne_zero hI
