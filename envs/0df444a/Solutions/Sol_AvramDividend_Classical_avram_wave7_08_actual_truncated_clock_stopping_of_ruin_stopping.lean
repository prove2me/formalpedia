-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:24:47.274981+00:00
-- url     : https://prove2.me/submissions/58086368-fe83-4fb6-b6a1-4c31c078b3c1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (hRuinStop : IsStoppingTime 𝓕.rightCont (ruinTime X x D)) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : WithTop ℝ≥0)) := by
  have hclock := avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  intro t
  change MeasurableSet[𝓕.rightCont t]
    {ω | ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal :
      WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}
  have hset :
      {ω | ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal :
        WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
      {ω | min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ (t : ℝ≥0∞)} := by
    ext ω
    change (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal :
      WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) ↔
      min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ (t : ℝ≥0∞)
    conv_rhs => rw [← hclock.1 ω]
    rfl
  rw [hset]
  by_cases hn : (n : ℝ≥0∞) ≤ (t : ℝ≥0∞)
  · have hall :
        {ω | min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
        (Set.univ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact le_trans (min_le_right _ _) hn
    rw [hall]
    exact MeasurableSet.univ
  · have hsource :
        {ω | min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
        {ω | ruinTime X x D ω ≤ (t : ℝ≥0∞)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        rcases min_le_iff.mp h with hσ | hn'
        · exact hσ
        · exact (hn hn').elim
      · intro hσ
        exact le_trans (min_le_left _ _) hσ
    rw [hsource]
    exact hRuinStop t