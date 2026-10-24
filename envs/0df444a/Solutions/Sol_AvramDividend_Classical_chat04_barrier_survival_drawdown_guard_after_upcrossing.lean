-- Prove2me | solution 1 for AvramDividend.Classical.chat04_barrier_survival_drawdown_guard_after_upcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:36:10.570108+00:00
-- url     : https://prove2.me/submissions/ff8c21eb-7500-4808-a452-b3adba68d441

import Mathlib.Data.Set.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Before barrier ruin, the post-upcrossing drawdown has not breached the ruin level. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (ω : Ω) (u : ℝ≥0)
    (hdraw : ∀ t : ℝ≥0,
      riskProcess X x (barrierStrategy X x a) t ω < 0 ↔
        a < runningSup X t ω - X.X t ω) :
    {t : ℝ≥0 | u < t ∧
      (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω} =
    {t : ℝ≥0 | u < t ∧
      (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω ∧
        ¬ a < runningSup X t ω - X.X t ω} := by
  ext t
  constructor
  · rintro ⟨htu, hsurv⟩
    have hn := riskProcess_nonneg_before_ruin X x
      (barrierStrategy X x a) ω t hsurv
    refine ⟨htu, hsurv, ?_⟩
    intro hb
    exact (not_lt_of_ge hn) ((hdraw t).2 hb)
  · rintro ⟨htu, hsurv, _⟩
    exact ⟨htu, hsurv⟩
