-- Prove2me | solution 1 for AvramDividend.Classical.levy_future_increment_indep_rightCont_prior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:16:43.101789+00:00
-- url     : https://prove2.me/submissions/085c3874-b779-4dfb-a840-f24fc7118415

import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u t : ℝ≥0) (hsu : s < u) (hut : u ≤ t) :
    Indep
      (MeasurableSpace.comap (fun ω => X.X t ω - X.X u ω) inferInstance)
      (𝓕.rightCont s) P := by
  have hsub : (𝓕.rightCont s) ≤ (𝓕 u) := by
    rw [𝓕.rightCont_eq s]
    exact iInf₂_le u hsu
  exact indep_of_indep_of_le_right (X.indepIncrements u t hut) hsub
