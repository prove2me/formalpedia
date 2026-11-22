-- Prove2me | solution 1 for Csg.CSG.stageValue_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:45:07.873433+00:00
-- url     : https://prove2.me/submissions/c5e6c73f-d3fa-4456-bb88-eaea3b9c87f6

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone
import Theorems.Thm_Csg_CSG_stageGame_A_lipschitz
import Theorems.Thm_Csg_MatrixGame_abs_value_sub_le


set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) : |C.stageValue s v - C.stageValue s w| ≤ ε := by
  change |(C.stageGame s v).value - (C.stageGame s w).value| ≤ ε
  exact MatrixGame.abs_value_sub_le fun a1 a2 => C.stageGame_A_lipschitz hε h a1 a2
end Csg.CSG
