-- Prove2me | solution 1 for Csg.CSG.stageGame_A_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:41:59.804206+00:00
-- url     : https://prove2.me/submissions/05bc6886-9a1c-4940-a6c9-e29a4a70f65e

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_expect_lipschitz

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) (a1 : A1) (a2 : A2) :
    |(C.stageGame s v).A a1 a2 - (C.stageGame s w).A a1 a2| ≤ ε := by
  have heq : (C.stageGame s v).A a1 a2 - (C.stageGame s w).A a1 a2 =
      C.expect s a1 a2 v - C.expect s a1 a2 w := by
    change (C.r s a1 a2 + C.expect s a1 a2 v) - (C.r s a1 a2 + C.expect s a1 a2 w) = _
    ring
  rw [heq]
  exact C.expect_lipschitz hε h
end Csg.CSG
