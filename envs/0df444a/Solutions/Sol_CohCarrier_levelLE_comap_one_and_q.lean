-- Prove2me | solution 1 for CohCarrier.levelLE_comap_one_and_q
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1e82733f-e2aa-586d-9887-ec1d4d661bd5

import Mathlib
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_levelLE_comap_one_and_q

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem solution (N q : ℕ) [NeZero N] [NeZero q] (H : Subgroup (ZMod N)ˣ) :
    LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) 1 ∧
    LevelLE N (N * q) H (H.comap (ZMod.unitsMap (dvd_mul_right N q))) q :=
  ⟨⟨dvd_mul_right N q, one_dvd _, fun u hu => hu⟩,
   ⟨dvd_mul_right N q, by rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne N))], fun u hu => hu⟩⟩

end S_CohCarrier_levelLE_comap_one_and_q
end P2MW
export P2MW.S_CohCarrier_levelLE_comap_one_and_q (solution)
