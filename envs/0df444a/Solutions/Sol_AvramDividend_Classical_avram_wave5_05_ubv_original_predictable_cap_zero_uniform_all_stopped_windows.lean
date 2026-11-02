-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_stopped_windows
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:30:56.625652+00:00
-- url     : https://prove2.me/submissions/9f50446d-ab00-4f09-ad38-12423572b28b

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
On ONE full P-event, cap-supported predictable generator densities
have zero physical-clock integral even after restriction to ANY
path-dependent stopping/localisation window, including those
beginning at zero or after recurrent cap contacts.
-/

/-- Uniform original cap-nullity for arbitrary path-dependent windows. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ (σ τ : Ω → ℝ≥0)
      (weight : ℝ≥0 → Ω → ℝ≥0∞),
      (∫⁻ t : ℝ≥0,
        if (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
              Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c) ∧
              (σ ω ≤ t ∧ t ≤ τ ω)
        then weight t ω else 0 ∂μ) = 0 := by
  have hUniform :=
    avram_wave5_05_ubv_original_predictable_cap_zero_uniform_all_characteristic_weights
      X hBV x c D hD hCap μ
  filter_upwards [hUniform] with ω hω
  intro σ τ weight
  have hWeighted :=
    hω (fun t ω => if σ ω ≤ t ∧ t ≤ τ ω then weight t ω else 0)
  calc
    (∫⁻ t : ℝ≥0,
      if (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c) ∧
            (σ ω ≤ t ∧ t ≤ τ ω)
      then weight t ω else 0 ∂μ) =
      ∫⁻ t : ℝ≥0,
        if 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω ∧
            Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
        then (if σ ω ≤ t ∧ t ≤ τ ω then weight t ω else 0)
        else 0 ∂μ := by
          apply lintegral_congr
          intro t
          by_cases hContact : 0 < t ∧
              (t : ℝ≥0∞) < ruinTime X x D ω ∧
              Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = c
          · by_cases hWindow : σ ω ≤ t ∧ t ≤ τ ω
            · simp [hContact, hWindow]
            · simp [hContact, hWindow]
          · simp [hContact]
    _ = 0 := hWeighted
