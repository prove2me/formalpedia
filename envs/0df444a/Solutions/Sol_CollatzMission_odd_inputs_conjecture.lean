-- Prove2me | solution 1 for CollatzMission.odd_inputs_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T00:29:51.206953+00:00
-- url     : https://prove2.me/submissions/e8a411a2-206f-4606-b9af-4e7af67efcca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CollatzMission
import Definitions.Def_collatzStepMap
import Definitions.Def_syracuseStep
import Theorems.Thm_collatz_reaches_syracuse_iterate
import Theorems.Thm_CollatzMission_syracuse_odd_conjecture

open CollatzMission in
theorem solution : OddInputsConjecture := by
  intro n hn hodd
  obtain ⟨t, ht⟩ := syracuse_odd_conjecture n hn hodd
  obtain ⟨m, hm⟩ := collatz_reaches_syracuse_iterate n hodd t
  exact ⟨m, hm.trans ht⟩
