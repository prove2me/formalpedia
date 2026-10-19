-- Prove2me | solution 1 for ConnesRigidity.FiniteCarry.carry_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/d683002d-dbae-404f-a288-03cc4c22ea4e

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
    carry (x + y) z = carry x z + carry y z := by
  simp [carry, add_mul]
end ConnesRigidity.FiniteCarry
