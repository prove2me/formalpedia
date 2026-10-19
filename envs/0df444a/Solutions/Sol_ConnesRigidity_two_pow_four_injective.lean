-- Prove2me | solution 1 for ConnesRigidity.two_pow_four_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/f2c2e4ae-1b24-4433-9c0c-b400024f9418

import Mathlib
import Definitions.Def_ConnesRigidity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
open Function
universe u v w z
namespace ConnesRigidity
theorem _root_.solution {m n : ℕ}
    (h : 2 ^ (4 * m) = 2 ^ (4 * n)) : m = n := by
  have hfour : 4 * m = 4 * n := Nat.pow_right_injective (by decide : 2 ≤ 2) h
  omega
end ConnesRigidity
