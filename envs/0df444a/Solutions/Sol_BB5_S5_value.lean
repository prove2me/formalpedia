-- Prove2me | solution 1 for BB5.S5_value
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-22T15:09:03.329571+00:00
-- url     : https://prove2.me/submissions/710cc627-c9be-42d9-887d-3d4f00a1547f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Theorems.Thm_BB5_lower_bound
import Theorems.Thm_BB5_upper_bound

theorem solution : FCP.BusyBeaver.BB 5 = 47176870 := by
  exact le_antisymm BB5.upper_bound BB5.lower_bound
