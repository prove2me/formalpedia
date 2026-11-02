-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:19:32.770353+00:00
-- url     : https://prove2.me/submissions/7b62b85a-d53d-4aa1-8be0-abc8bbdbd05d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_positive_no_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < σ ω →
        0 < riskProcess X x D t ω := by
  have hpre : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ riskProcess X x D s ω := by
    intro ω s hs
    exact riskProcess_nonneg_before_ruin X x D ω s hs
  have hzero :
      ∀ᵐ ω ∂P, ((0 : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω →
        0 < riskProcess X x D 0 ω :=
    avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
      X hBV x D hD.1.1 hpre (fun _ : Ω => (0 : ℝ≥0))
      (by intro s; simp) (by intro s; simp)
  have hpos := avram_wave5_ubv_allcap_original_stopped_positive_no_grid
    X hBV x C D hD σ hσ μ
  filter_upwards [hpos, hzero] with ω hω hωzero
  filter_upwards [hω] with t ht
  intro htime
  by_cases htzero : t = 0
  · subst t
    exact hωzero (lt_of_lt_of_le htime (hσ ω))
  · exact ht ⟨(pos_iff_ne_zero).2 htzero, htime⟩
