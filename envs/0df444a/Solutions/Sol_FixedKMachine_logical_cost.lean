-- Prove2me | solution 1 for FixedKMachine.logical_cost
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:03:07.627742+00:00
-- url     : https://prove2.me/submissions/71d84128-644f-49bd-9793-c8ae9683b9fe

import Mathlib
open MeasureTheory Set

theorem solution (H N : Prop) (hRH : H → ¬N) :
    (N → H) ↔ ¬N := by
  constructor
  · intro h hN
    exact hRH (h hN) hN
  · intro h hN
    exact False.elim (h hN)
