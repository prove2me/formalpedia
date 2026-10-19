-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_drawdown_survival_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:21:14.775907+00:00
-- url     : https://prove2.me/submissions/9a653350-96cd-49d0-b566-65fcf0220cbc

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_drawdown_exit_event_sandwich
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
    ((∀ t : ℝ≥0, t < u → b - a ≤ X.X t ω) →
      (∀ t : ℝ≥0, t < u →
        runningSup X t ω - X.X t ω ≤ a)) ∧
    ((∀ t : ℝ≥0, t < u →
        runningSup X t ω - X.X t ω ≤ a) →
      (∀ t : ℝ≥0, t < u → -a ≤ X.X t ω)) := by
  obtain ⟨hLower, hUpper⟩ :=
    firstUpcrossing_drawdown_exit_event_sandwich X a b ω u hu
  constructor
  · intro hRaw t ht
    apply le_of_not_gt
    intro hDraw
    have hx : X.X t ω < b - a :=
      (hUpper ⟨ht, hDraw⟩).2
    exact (not_lt_of_ge (hRaw t ht)) hx
  · intro hDraw t ht
    apply le_of_not_gt
    intro hx
    have hBad : a < runningSup X t ω - X.X t ω :=
      (hLower ⟨ht, hx⟩).2
    exact (not_lt_of_ge (hDraw t ht)) hBad
