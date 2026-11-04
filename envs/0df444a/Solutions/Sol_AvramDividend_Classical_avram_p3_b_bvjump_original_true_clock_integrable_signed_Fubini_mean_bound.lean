-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_true_clock_integrable_signed_Fubini_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:37:01.924124+00:00
-- url     : https://prove2.me/submissions/61d61bb5-b59c-4a05-90ea-706291236d0a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_physical_clock_total_mass_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine L1 Fubini passage for the original finite physical stopped clock:
a nonpositive time-path expected signed residual yields an integrable
pathwise time integral of the same residual with nonpositive mean. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (T : ℝ≥0) (F : ℝ≥0 × Ω → ℝ)
    (hFint : Integrable F
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P))
    (hFmean : (∫ p, F p ∂((((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) ≤ 0) :
    Integrable (fun ω => (∫ t, F (t, ω)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal))) P ∧
    (∫ ω, (∫ t, F (t, ω)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal)) ∂P) ≤ 0 := by
  let clock : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal
  have hclock : clock Set.univ < ∞ :=
    avram_p3_b_bvjump_original_physical_clock_total_mass_finite T
  letI : IsFiniteMeasure clock := ⟨hclock⟩
  constructor
  · exact hFint.integral_prod_right
  · rw [← integral_prod_symm F hFint]
    exact hFmean
