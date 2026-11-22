-- Prove2me | solution 1 for Csg.CSG.stageGame_A_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:38:49.783421+00:00
-- url     : https://prove2.me/submissions/8d86cd07-8397-4a79-a0f7-4054e98faadd

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_expect_le_one

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', v s' ≤ 1) (a1 : A1) (a2 : A2) : (C.stageGame s v).A a1 a2 ≤ 1 := by
  change C.r s a1 a2 + C.expect s a1 a2 v ≤ 1
  rw [hr s a1 a2, zero_add]
  exact C.expect_le_one hv
end Csg.CSG
