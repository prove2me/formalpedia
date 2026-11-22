-- Prove2me | solution 1 for Csg.CSG.stageGame_A_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:37:49.694509+00:00
-- url     : https://prove2.me/submissions/3b9ba182-eca1-4752-a9f4-619ffcc5652e

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_expect_mono

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution {s : S} {v w : S → ℝ} (hle : ∀ s', v s' ≤ w s') (a1 : A1) (a2 : A2) :
    (C.stageGame s v).A a1 a2 ≤ (C.stageGame s w).A a1 a2 := by
  change C.r s a1 a2 + C.expect s a1 a2 v ≤ C.r s a1 a2 + C.expect s a1 a2 w
  have h : C.expect s a1 a2 v ≤ C.expect s a1 a2 w := C.expect_mono hle
  linarith
end Csg.CSG
