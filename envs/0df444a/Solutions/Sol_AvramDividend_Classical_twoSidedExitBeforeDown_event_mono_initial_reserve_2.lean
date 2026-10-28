-- Prove2me | solution 2 for AvramDividend.Classical.twoSidedExitBeforeDown_event_mono_initial_reserve
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:56:03.426543+00:00
-- url     : https://prove2.me/submissions/6aa22f52-fd4e-42b8-a012-68a8b000b5b9

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_mono_bounds
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x y : ℝ) (hxy : x ≤ y) :
    {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ⊆
    {ω : Ω | twoSidedExitUpTime X (a - y) ω <
      twoSidedExitDownTime X (-y) ω} :=
  twoSidedExitBeforeDown_event_mono_bounds X (a - y) (a - x) (-y) (-x) (by linarith) (by linarith)