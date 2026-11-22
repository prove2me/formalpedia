-- Prove2me | solution 1 for Csg.CSG.stageValue_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:41:56.304224+00:00
-- url     : https://prove2.me/submissions/06a46552-b1a6-43a3-b289-71496faaf554

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_stageGame_A_le_one
import Theorems.Thm_Csg_MatrixGame_value_le_of_forall_le


set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', v s' ≤ 1) : C.stageValue s v ≤ 1 := by
  change (C.stageGame s v).value ≤ (1:ℝ)
  exact (C.stageGame s v).value_le_of_forall_le fun a1 a2 => C.stageGame_A_le_one hr hv a1 a2
end Csg.CSG
