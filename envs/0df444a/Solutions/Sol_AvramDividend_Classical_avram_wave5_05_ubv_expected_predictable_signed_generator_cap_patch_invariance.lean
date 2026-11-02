-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_expected_predictable_signed_generator_cap_patch_invariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:05:10.640108+00:00
-- url     : https://prove2.me/submissions/a90889ee-42cd-4a01-9a1c-f2f6a5742105

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_signed_generator_cap_value_patch_integral_independence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
The signed original compensated source generator's
expected physical-clock drift is insensitive to every
arbitrary boundary value patch at true predictable cap
contact. No cap derivative or full controlled Itô formula.
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
    ∀ (F G : ℝ≥0 → Ω → ℝ),
      (∀ (ω : Ω) (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≠ c →
        F t ω = G t ω) →
      (∫ ω : Ω, ∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then F t ω else 0 ∂μ ∂P) =
      (∫ ω : Ω, ∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then G t ω else 0 ∂μ ∂P) := by
  have hPath :=
    avram_wave5_05_ubv_original_predictable_signed_generator_cap_value_patch_integral_independence
      X hBV x c D hD hCap μ
  intro F G hFG
  apply integral_congr_ae
  filter_upwards [hPath] with ω hω
  exact hω F G (fun t htPos htLive hOffCap =>
    hFG ω t htPos htLive hOffCap)
