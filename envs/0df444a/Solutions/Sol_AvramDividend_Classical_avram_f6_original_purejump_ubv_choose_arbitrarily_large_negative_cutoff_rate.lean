-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_purejump_ubv_choose_arbitrarily_large_negative_cutoff_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:11:04.77326+00:00
-- url     : https://prove2.me/submissions/441f08a7-3882-4fa3-b096-50d3b8e899c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_purejump_ubv_truncated_negative_rates_diverge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0)
    (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ R ≤ (X.ν (Iio (-δ))).toReal := by
  have hlim :=
    avram_f6_original_purejump_ubv_truncated_negative_rates_diverge X hBV hσ
  have hAbove : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      R ≤ (X.ν (Iio (-δ))).toReal :=
    hlim.eventually (eventually_ge_atTop R)
  have hPositive : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hBound⟩ := (hPositive.and hAbove).exists
  exact ⟨δ, hδ, hBound⟩
