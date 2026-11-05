-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_finite_cap_linear_extension_global_exponential_envelope_of_interior_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:32:22.457702+00:00
-- url     : https://prove2.me/submissions/acc68544-9600-4afe-ae8d-8c0f4d40b88a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded interior dividend value gives a global exponential envelope for
the actual finite-cap linear extension, including all negative reserves. -/
theorem solution
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (w V : ℝ → ℝ)
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal))
    (M : ℝ) (hM : 0 ≤ M)
    (hw_bd : ∀ z ∈ Icc (0 : ℝ) C.toReal, ‖w z‖ ≤ M) :
    ∀ z : ℝ, ‖V z‖ ≤ (M + 1) * Real.exp z := by
  intro z
  have hcap : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hK : 0 ≤ M + 1 := by positivity
  have hexp : 0 < Real.exp z := Real.exp_pos z
  by_cases hzcap : z ≤ C.toReal
  · rw [hVfinite hC z, if_pos hzcap]
    by_cases hz0 : z < 0
    · rw [hw_neg z hz0]
      simp only [norm_zero]
      exact mul_nonneg hK hexp.le
    · have hz0' : 0 ≤ z := le_of_not_gt hz0
      have hb : ‖w z‖ ≤ M := hw_bd z ⟨hz0', hzcap⟩
      have he : (1 : ℝ) ≤ Real.exp z := by
        have he' := Real.add_one_le_exp z
        linarith
      nlinarith
  · have hzgt : C.toReal < z := lt_of_not_ge hzcap
    have hz : 0 ≤ z := le_trans hcap hzgt.le
    have hnonneg : 0 ≤ z - C.toReal := sub_nonneg.mpr hzgt.le
    have hBoundCap : ‖w C.toReal‖ ≤ M :=
      hw_bd C.toReal ⟨hcap, le_refl _⟩
    rw [hVfinite hC z, if_neg hzcap]
    have htriangle : ‖w C.toReal + (z - C.toReal)‖ ≤
        ‖w C.toReal‖ + ‖z - C.toReal‖ := norm_add_le _ _
    have hsubnorm : ‖z - C.toReal‖ = z - C.toReal := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    rw [hsubnorm] at htriangle
    have hsimple : ‖w C.toReal + (z - C.toReal)‖ ≤ M + z := by
      linarith
    have he := Real.add_one_le_exp z
    have he1 : (1 : ℝ) ≤ Real.exp z := by linarith
    nlinarith
