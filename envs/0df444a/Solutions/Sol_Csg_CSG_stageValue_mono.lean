-- Prove2me | solution 1 for Csg.CSG.stageValue_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:40:46.172395+00:00
-- url     : https://prove2.me/submissions/eaa736c2-dc68-4568-a33a-ec56ac28643d

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_stageGame_A_mono
import Theorems.Thm_Csg_MatrixGame_value_mono


set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution {s : S} {v w : S → ℝ} (hle : ∀ s', v s' ≤ w s') :
    C.stageValue s v ≤ C.stageValue s w := by
  change (C.stageGame s v).value ≤ (C.stageGame s w).value
  exact MatrixGame.value_mono fun a1 a2 => C.stageGame_A_mono hle a1 a2
end Csg.CSG
