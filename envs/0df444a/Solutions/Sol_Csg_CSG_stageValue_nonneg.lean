-- Prove2me | solution 1 for Csg.CSG.stageValue_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:41:01.812449+00:00
-- url     : https://prove2.me/submissions/b3ad4c7c-3c1a-490d-be53-69a957a283c8

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_stageGame_A_nonneg
import Theorems.Thm_Csg_MatrixGame_le_value_of_forall_le


set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', 0 ≤ v s') : 0 ≤ C.stageValue s v := by
  change (0:ℝ) ≤ (C.stageGame s v).value
  exact (C.stageGame s v).le_value_of_forall_le fun a1 a2 => C.stageGame_A_nonneg hr hv a1 a2
end Csg.CSG
