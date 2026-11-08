-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_raw_R_bounded_stopping_clock_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:29:34.797566+00:00
-- url     : https://prove2.me/submissions/14de2757-4e20-4c2d-a70d-40a3cbec62a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_raw_R_nonnegative_bounded_clock
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_fixed_time_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An a.e. measurable sample of the literal original BV jump residual
at a random clock bounded by T inherits fixed-clock L¹. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P, τ ω ≤ T)
    (hMeas : AEStronglyMeasurable (fun ω =>
      (((τ ω : ℝ≥0) : ℝ) * X.drift - X.X (τ ω) ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ τ ω then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)) P) :
    Integrable (fun ω =>
      (((τ ω : ℝ≥0) : ℝ) * X.drift - X.X (τ ω) ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ τ ω then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)) P := by
  classical
  let R : Ω → ℝ≥0 → ℝ := fun ω t =>
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0)
  change Integrable (fun ω => R ω (τ ω)) P
  have hInt : Integrable (fun ω => R ω T) P := by
    simpa only [R] using
      (avram_bv_residual10_original_raw_R_fixed_time_L1 X hX hBV T)
  have hM : AEStronglyMeasurable (fun ω => R ω (τ ω)) P := by
    simpa only [R] using hMeas
  have hDom : ∀ᵐ ω ∂P, ‖R ω (τ ω)‖ ≤ R ω T := by
    filter_upwards
      [avram_bv_residual9_original_raw_R_nonnegative_bounded_clock X hBV T, hτ]
      with ω hω hτw
    change R ω 0 = 0 ∧
      ∀ t : ℝ≥0, t ≤ T → 0 ≤ R ω t ∧ R ω t ≤ R ω T at hω
    have hb := hω.2 (τ ω) hτw
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  exact hInt.mono' hM hDom
