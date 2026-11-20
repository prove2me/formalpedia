-- Prove2me | solution 1 for DeletionCode.OverlapCollision.collision_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:47.923334+00:00
-- url     : https://prove2.me/submissions/38b13e82-2cea-4f5f-b01d-492f1b1434e1

import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OverlapCollision
import Theorems.Thm_DeletionCode_OverlapCollision_collisionEncode_injective

set_option autoImplicit true
open DeletionCode DeletionCode.OverlapCollision
open Windows HeaderRecovery
namespace DeletionCode.OverlapCollision
theorem _root_.solution (n k a b : ℕ) (hab : a < b)
    (_ha : a + k ≤ n) (hb : b + k ≤ n) :
    Fintype.card (Collision n k a b) ≤ 2 ^ (n - k) := by
  calc
    Fintype.card (Collision n k a b) ≤ Fintype.card (Bits (n - k)) :=
      Fintype.card_le_of_injective (collisionEncode n k a b hb)
        (collisionEncode_injective n k a b hab hb)
    _ = 2 ^ (n - k) := by simp [Bits]
end DeletionCode.OverlapCollision
