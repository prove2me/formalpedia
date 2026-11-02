-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_cap_zero_uniform_all_source_mark_measures
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:17:50.138183+00:00
-- url     : https://prove2.me/submissions/15b2e334-b055-4609-96c8-9a0b2cb00ca5

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_characteristic_weights

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
For a fixed atomless physical clock, the original predictable cap-null
event is uniform over every mark measure ν and every nonnegative
mark-dependent source compensator density, even chosen after ω.
-/

/-- Uniform in the Lévy mark measure and characteristic weight: exact
    original predictable cap contact has zero marked physical-time mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ (ν : Measure ℝ) (weight : ℝ≥0 → ℝ → Ω → ℝ≥0∞),
      (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν ∂μ) = 0 := by
  have hUniform :=
    avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_characteristic_weights
      X hBV x c D hD hCap μ
  filter_upwards [hUniform] with ω hω
  intro ν weight
  have hWeighted :=
    hω (fun t ω => ∫⁻ z : ℝ, weight t z ω ∂ν)
  have hPoint (t : ℝ≥0) :
      (∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν) =
      (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
       then (∫⁻ z : ℝ, weight t z ω ∂ν) else 0) := by
    by_cases ht : 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
    · simp [ht]
    · simp [ht]
  calc
    (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
      if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
      then weight t z ω else 0 ∂ν ∂μ) =
      ∫⁻ t : ℝ≥0,
        (if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
         then (∫⁻ z : ℝ, weight t z ω ∂ν) else 0) ∂μ := by
        exact lintegral_congr hPoint
    _ = 0 := hWeighted
