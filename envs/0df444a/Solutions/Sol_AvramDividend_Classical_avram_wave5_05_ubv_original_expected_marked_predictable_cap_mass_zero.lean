-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_expected_marked_predictable_cap_mass_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:55:11.221205+00:00
-- url     : https://prove2.me/submissions/8330b68a-052b-4c81-a103-0e122171c5c6

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_cap_zero_uniform_all_source_mark_measures

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
The genuine original source compensator contributes no
positive expected marked physical-clock mass at the exact
predictable cap, for any deterministic mark measure and
any path-dependent nonnegative characteristic weight.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ (ν : Measure ℝ) (weight : ℝ≥0 → ℝ → Ω → ℝ≥0∞),
      (∫⁻ ω : Ω, ∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν ∂μ ∂P) = 0 := by
  have hPath :=
    avram_wave5_05_ubv_original_cap_zero_uniform_all_source_mark_measures
      X hBV x c D hD hCap μ
  intro ν weight
  have hZero : ∀ᵐ ω ∂P,
      (∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then weight t z ω else 0 ∂ν ∂μ) = 0 := by
    filter_upwards [hPath] with ω hω
    exact hω ν weight
  calc
    (∫⁻ ω : Ω, ∫⁻ t : ℝ≥0, ∫⁻ z : ℝ,
      if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
      then weight t z ω else 0 ∂ν ∂μ ∂P) =
        (∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P) :=
      lintegral_congr_ae hZero
    _ = 0 := by simp