-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_marked_source_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:44:40.968045+00:00
-- url     : https://prove2.me/submissions/de6e5d22-2d2a-4cd3-879e-2f88fec5ce96

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
The exact predictable cap-contact slice of a Lévy mark-integrated
characteristic has zero dt-mass on the original controlled UBV process.
There is no assumption that the mark density is finite at the cap.
-/

/-- A marked nonnegative compensator density supported on genuine
    predictable cap contact has vanishing original atomless time integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ]
    (ν : Measure ℝ)
    (weight : ℝ≥0 → ℝ → Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν ∂μ) = 0 := by
  have hWeighted :=
    avram_wave5_05_ubv_original_predictable_cap_contact_weighted_atomless_zero
      X hBV x c D hD hCap μ
      (fun t ω => ∫⁻ z : ℝ, weight t z ω ∂ν)
  filter_upwards [hWeighted] with ω hω
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
    _ = 0 := hω
