-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_weighted_log_image_integral_eq_source_test
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:17:19.96547+00:00
-- url     : https://prove2.me/submissions/4c551b8f-028b-4f95-a37e-51083ec6a174

import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_weighted_log_inverse_for_negative_tests_all_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- A negative-supported source test equals its fourth-weighted log-image integral. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hfpos : ∀ y : ℝ, 0 ≤ y → f y = 0) :
    (∫ z : ℝ, f (Real.log z) / (z - 1) ^ 4 ∂
      ((μ.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (Y ω) - 1) ^ 4))).map
        (fun ω => Real.exp (Y ω)))) =
    ∫ ω, f (Y ω) ∂μ := by
  let w : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ((Real.exp (Y ω) - 1) ^ 4)
  let g : ℝ → ℝ := fun z => f (Real.log z) / (z - 1) ^ 4
  have hw : Measurable w := by
    fun_prop
  have hwfin : ∀ᵐ ω ∂μ, w ω < ⊤ := by
    filter_upwards [] with ω
    simp [w]
  have hmap : Measurable (fun ω => Real.exp (Y ω)) := by
    fun_prop
  have hg : Measurable g := by
    fun_prop
  have heq (ω : Ω) :
      (w ω).toReal • g (Real.exp (Y ω)) = f (Y ω) := by
    have hnonneg : 0 ≤ (Real.exp (Y ω) - 1) ^ 4 := by positivity
    dsimp [w, g]
    rw [ENNReal.toReal_ofReal hnonneg]
    exact AvramDividend.Classical.avram_p2_i_moment_weighted_log_inverse_for_negative_tests_all_real
      f hfpos (Y ω)
  change (∫ z : ℝ, g z ∂((μ.withDensity w).map
    (fun ω => Real.exp (Y ω)))) = ∫ ω, f (Y ω) ∂μ
  calc
    _ = ∫ ω, g (Real.exp (Y ω)) ∂(μ.withDensity w) := by
      exact integral_map hmap.aemeasurable hg.aestronglyMeasurable
    _ = ∫ ω, (w ω).toReal • g (Real.exp (Y ω)) ∂μ := by
      exact integral_withDensity_eq_integral_toReal_smul hw hwfin _
    _ = ∫ ω, f (Y ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact heq ω
