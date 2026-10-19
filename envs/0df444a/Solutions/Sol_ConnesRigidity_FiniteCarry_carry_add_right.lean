-- Prove2me | solution 1 for ConnesRigidity.FiniteCarry.carry_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/0d43bd73-4129-4a8a-b215-8094101ef433

import Mathlib
import Definitions.Def_ConnesRigidity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
open ConnesRigidity.FiniteCarry
namespace ConnesRigidity.FiniteCarry
theorem _root_.solution (x y z : Bit) :
    carry x (y + z) = carry x y + carry x z := by
  simp [carry, mul_add]
end ConnesRigidity.FiniteCarry
