-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_infinite_cap_stopped_interior_density_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:28:46.138004+00:00
-- url     : https://prove2.me/submissions/886fa665-6cc2-4829-87bb-728acfdb0273

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The original cap-infinite generator density has no upper contact boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x ⊤ D)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ ω, τ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ]
    (F : ℝ → ℝ)
    (hF : ∀ y : ℝ, 0 < y → F y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      (t : ℝ≥0∞) < τ ω →
      F (riskProcess X x D t ω) ≤ 0 := by
  have hPositive :=
    avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
      X hBV x (⊤ : ℝ≥0∞) D hD τ hτ μ
  filter_upwards [hPositive] with ω hω
  filter_upwards [hω] with t ht
  intro hBefore
  exact hF _ (ht hBefore)
