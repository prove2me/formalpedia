-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_zero_ruin_event_rightcont_initial_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:17:17.709519+00:00
-- url     : https://prove2.me/submissions/66bd09be-61ef-4261-9d70-7797a8bcbd63

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | ruinTime X x D ω = 0} ∧
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | ruinTime X x D ω ≠ 0} := by
  have hDS : IsDividendStrategy 𝓕 D := hD.1.1
  have hStop := ruinTime_stopping_rightCont_filtration X x D hDS
  have hZero :
      MeasurableSet[𝓕.rightCont 0]
        {ω : Ω | ruinTime X x D ω ≤ (0 : ℝ≥0∞)} := hStop 0
  have hSets :
      {ω : Ω | ruinTime X x D ω = 0} =
        {ω : Ω | ruinTime X x D ω ≤ (0 : ℝ≥0∞)} := by
    ext ω
    simp
  have hEvent :
      MeasurableSet[𝓕.rightCont 0] {ω : Ω | ruinTime X x D ω = 0} := by
    rw [hSets]
    exact hZero
  exact ⟨hEvent, hEvent.compl⟩
