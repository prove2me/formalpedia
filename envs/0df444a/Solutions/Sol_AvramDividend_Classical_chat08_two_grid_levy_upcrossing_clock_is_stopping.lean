-- Prove2me | solution 1 for AvramDividend.Classical.chat08_two_grid_levy_upcrossing_clock_is_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:57:03.377957+00:00
-- url     : https://prove2.me/submissions/87e39a3b-6baf-48e6-ba88-35872be81781

import Theorems.Thm_AvramDividend_Classical_chat08_stopping_time_early_observed_switch
import Theorems.Thm_AvramDividend_Classical_chat08_two_level_levy_upcrossing_clock_stopping_time
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-! First recorded threshold hit on two deterministic grid observations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (a : ℝ) :
    IsStoppingTime ℱ
      (fun ω => if a < X.X s ω then (s : WithTop ℝ≥0)
        else if a < X.X t ω then (t : WithTop ℝ≥0)
        else (u : WithTop ℝ≥0)) := by
  let τ : Ω → WithTop ℝ≥0 := fun ω =>
    if a < X.X t ω then (t : WithTop ℝ≥0)
    else (u : WithTop ℝ≥0)
  have hτ : IsStoppingTime ℱ τ :=
    chat08_two_level_levy_upcrossing_clock_stopping_time X t u htu a
  have hlater : ∀ ω, (s : WithTop ℝ≥0) ≤ τ ω := by
    intro ω
    by_cases hhit : a < X.X t ω
    · change (s : WithTop ℝ≥0) ≤
        (if a < X.X t ω then (t : WithTop ℝ≥0) else (u : WithTop ℝ≥0))
      rw [if_pos hhit]
      exact_mod_cast hst
    · change (s : WithTop ℝ≥0) ≤
        (if a < X.X t ω then (t : WithTop ℝ≥0) else (u : WithTop ℝ≥0))
      rw [if_neg hhit]
      exact_mod_cast hst.trans htu
  have hA : MeasurableSet[ℱ s] {ω | a < X.X s ω} :=
    measurableSet_lt measurable_const (X.adapted s)
  simpa only [Set.mem_setOf_eq] using
    (chat08_stopping_time_early_observed_switch
      ℱ s {ω | a < X.X s ω} hA τ hτ hlater)
