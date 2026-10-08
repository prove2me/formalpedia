-- Prove2me | solution 1 for AvramDividend.Classical.monotone_rightJump_support_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:12:05.895541+00:00
-- url     : https://prove2.me/submissions/c5f68b51-2f74-4745-bebc-b72dc4d4e363

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution (f : ℝ → ℝ) (hf : Monotone f) :
    Set.Countable {t : ℝ | Function.rightLim f t ≠ f t} := by
  refine hf.countable_not_continuousAt.mono ?_
  intro t ht
  change Function.rightLim f t ≠ f t at ht
  intro hc
  exact ht (hc.continuousWithinAt (s := Ici t)).rightLim_eq
