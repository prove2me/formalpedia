-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_drawdown_exit_event_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:07:15.656978+00:00
-- url     : https://prove2.me/submissions/efb3cd08-aff7-4d8d-84d0-2ea4a2e1f379

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_drawdown_prepeak_exit_event_inclusions
import Theorems.Thm_AvramDividend_Classical_runningSup_pre_firstUpcrossing_between
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    {t : ℝ≥0 | t < u ∧ X.X t ω < -a} ⊆
      {t : ℝ≥0 | t < u ∧ a < runningSup X t ω - X.X t ω} ∧
    {t : ℝ≥0 | t < u ∧ a < runningSup X t ω - X.X t ω} ⊆
      {t : ℝ≥0 | t < u ∧ X.X t ω < b - a} := by
  have hprefix :
      ∀ t ∈ ({t : ℝ≥0 | t < u} : Set ℝ≥0),
        0 ≤ runningSup X t ω ∧ runningSup X t ω ≤ b := by
    intro t ht
    exact (runningSup_pre_firstUpcrossing_between X b ω u hu) t ht
  exact drawdown_prepeak_exit_event_inclusions
    {t : ℝ≥0 | t < u}
    (fun t => runningSup X t ω) (fun t => X.X t ω) a b hprefix
