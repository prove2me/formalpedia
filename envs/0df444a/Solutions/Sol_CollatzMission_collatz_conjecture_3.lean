-- Prove2me | solution 3 for CollatzMission.collatz_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T05:41:33.830919+00:00
-- url     : https://prove2.me/submissions/6ac82b53-21f6-4e5c-ac18-5a4466759b45
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CollatzMission
import Definitions.Def_collatzStepMap
import Theorems.Thm_CollatzMission_collatz_of_no_cycles_and_no_divergence
import Theorems.Thm_CollatzMission_no_divergent_counterexamples
import Theorems.Thm_CollatzMission_no_eventual_cycle_counterexamples

theorem solution (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, collatzStep^[m] n = 1 := by
  have h := CollatzMission.collatz_of_no_cycles_and_no_divergence
    CollatzMission.no_eventual_cycle_counterexamples
    CollatzMission.no_divergent_counterexamples n hn
  have hstep : collatzStep = CollatzMission.collatzStep := rfl
  rw [hstep]
  exact h
