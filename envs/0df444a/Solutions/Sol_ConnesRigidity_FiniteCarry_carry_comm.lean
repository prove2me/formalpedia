-- Prove2me | solution 1 for ConnesRigidity.FiniteCarry.carry_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/ad57c9c3-e074-40f9-a68d-161f23c94e9a

import Mathlib
import Definitions.Def_ConnesRigidity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
open ConnesRigidity.FiniteCarry
namespace ConnesRigidity.FiniteCarry
theorem _root_.solution (x y : Bit) : carry x y = carry y x := by
  simp [carry, mul_comm]
end ConnesRigidity.FiniteCarry
