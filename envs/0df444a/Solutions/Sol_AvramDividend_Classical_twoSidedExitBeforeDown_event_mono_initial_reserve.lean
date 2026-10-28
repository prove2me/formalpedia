-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitBeforeDown_event_mono_initial_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:55:14.087893+00:00
-- url     : https://prove2.me/submissions/449edc66-ffc9-49ca-86ac-1be4cd71d74c

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_mono_bounds
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Upper-first passage event is increasing in the initial reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x y : ℝ) (hxy : x ≤ y) :
    {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ⊆
    {ω : Ω | twoSidedExitUpTime X (a - y) ω <
      twoSidedExitDownTime X (-y) ω} := by
  exact twoSidedExitBeforeDown_event_mono_bounds
    X (a - y) (a - x) (-y) (-x) (by linarith) (by linarith)
