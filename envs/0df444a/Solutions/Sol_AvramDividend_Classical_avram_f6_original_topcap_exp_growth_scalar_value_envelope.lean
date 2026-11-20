-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_topcap_exp_growth_scalar_value_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:42:23.819184+00:00
-- url     : https://prove2.me/submissions/d7f39221-d5b7-4bb2-8570-474406562854

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_pos : ∀ y : ℝ, 0 ≤ y → 0 ≤ w y)
    (θ K : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hw_exp : ∀ y : ℝ, 0 ≤ y →
      w y ≤ K * Real.exp (θ * y))
    (S z : ℝ) (hzS : z ≤ S) :
    |w z| ≤ K * Real.exp (θ * S) := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg (hw_pos z hz)]
    calc
      w z ≤ K * Real.exp (θ * z) := hw_exp z hz
      _ ≤ K * Real.exp (θ * S) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hzS hθ
  · rw [hw_neg z (lt_of_not_ge hz)]
    simp only [abs_zero]
    exact mul_nonneg hK (Real.exp_pos _).le
