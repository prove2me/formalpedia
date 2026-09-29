-- Prove2me | solution 2 for CollatzMission.collatz_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T05:40:18.006054+00:00
-- url     : https://prove2.me/submissions/540d6485-5e81-44b9-b361-69fdda0f9524
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CollatzMission
import Definitions.Def_collatzStepMap
import Theorems.Thm_CollatzMission_collatz_of_odd_inputs
import Theorems.Thm_CollatzMission_odd_inputs_conjecture

theorem solution (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, collatzStep^[m] n = 1 := by
  have h := CollatzMission.collatz_of_odd_inputs CollatzMission.odd_inputs_conjecture n hn
  have hstep : collatzStep = CollatzMission.collatzStep := rfl
  rw [hstep]
  exact h
