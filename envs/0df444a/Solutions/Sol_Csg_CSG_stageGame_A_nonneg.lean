-- Prove2me | solution 1 for Csg.CSG.stageGame_A_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:38:08.236415+00:00
-- url     : https://prove2.me/submissions/910c00fa-d3d1-4c22-8c86-1a5943283c32

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_expect_nonneg

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (hr : ∀ s a1 a2, C.r s a1 a2 = 0) {s : S} {v : S → ℝ}
    (hv : ∀ s', 0 ≤ v s') (a1 : A1) (a2 : A2) : 0 ≤ (C.stageGame s v).A a1 a2 := by
  change 0 ≤ C.r s a1 a2 + C.expect s a1 a2 v
  rw [hr s a1 a2, zero_add]
  exact C.expect_nonneg hv
end Csg.CSG
