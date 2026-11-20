-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_true_ruinclipped_subordinate_clock_positive_interior_before_contact_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:52:02.204883+00:00
-- url     : https://prove2.me/submissions/9f0ee194-8712-455e-80c9-674368bdf2e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hUBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < (ρ ω : ℝ≥0∞) →
        0 < riskProcess X x D t ω := by
  have hClock :=
    avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ ρ hτeq hρle
  exact
    avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
      X hUBV x C D hD (fun ω => (ρ ω : ℝ≥0∞)) hClock.2 μ

