-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_signed_generator_cap_patch_countable_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:31:01.127097+00:00
-- url     : https://prove2.me/submissions/ff0fc854-7e40-42d6-90a4-91cd506d5755

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
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
Countably many fixed atomless generator clocks share a single
P-conull event on which every signed original predictable drift
integral is invariant under arbitrary cap-only changes, including
when the original strategy starts at the cap.
-/

/-- Uniform countable-clock signed cap-generator patch independence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : ℕ → Measure ℝ≥0)
    (hsf : ∀ n, SFinite (μ n))
    (hatom : ∀ n, NullSingletonClass (μ n)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ (F G : ℝ≥0 → Ω → ℝ),
      (∀ t : ℝ≥0, 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≠ c →
        F t ω = G t ω) →
      (∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then F t ω else 0 ∂μ n) =
      (∫ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω
        then G t ω else 0 ∂μ n) := by
  apply (ae_all_iff).2
  intro n
  letI : SFinite (μ n) := hsf n
  letI : NullSingletonClass (μ n) := hatom n
  exact
    avram_wave5_05_ubv_original_predictable_signed_generator_cap_value_patch_integral_independence
      X hBV x c D hD hCap (μ n)
