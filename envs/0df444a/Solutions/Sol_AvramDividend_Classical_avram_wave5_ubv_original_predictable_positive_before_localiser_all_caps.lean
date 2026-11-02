-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_predictable_positive_before_localiser_all_caps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:33:55.063856+00:00
-- url     : https://prove2.me/submissions/d24554d2-297a-4462-a7de-10523a45b197

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t := by
  have hpos := avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
    X hBV x C D hD σ hσ μ
  have heq := avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
    X x D hD.1.1 μ
  filter_upwards [hpos, heq] with ω hωpos hωeq
  filter_upwards [hωpos, hωeq] with t htpos hteq
  intro htime
  rw [hteq htime.1]
  exact htpos htime.2
