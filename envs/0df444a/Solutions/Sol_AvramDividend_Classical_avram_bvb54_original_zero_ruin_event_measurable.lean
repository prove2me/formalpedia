-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb54_original_zero_ruin_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:59:36.306238+00:00
-- url     : https://prove2.me/submissions/234c1f85-d8df-4351-8a9e-bd0f1af7d3ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_ruin_event_rightcont_initial_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    MeasurableSet {ω : Ω | ruinTime X x D ω = 0} := by
  have hZero : MeasurableSet[𝓕.rightCont 0]
      {ω : Ω | ruinTime X x D ω = 0} :=
    (avram_ubv_hor3_original_zero_ruin_event_rightcont_initial_measurable
      X x C D hD).1
  exact (𝓕.rightCont.le 0) _ hZero
