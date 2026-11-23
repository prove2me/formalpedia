-- Prove2me | solution 1 for Csg.CSG.bwInd_succ_row_optimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:29:46.048666+00:00
-- url     : https://prove2.me/submissions/8a488e68-69a2-49da-b60b-27df71ad344c

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BackwardInduction
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_MatrixGame_value_row_optimal

attribute [local simp] Csg.CSG.bwInd_zero

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (rFin : S → ℝ) (n : ℕ) (s : S) :
    ∀ p' ∈ stdSimplex ℝ A1,
      C.bwInd rFin (n + 1) s ≤ (C.stageGame s (C.bwInd rFin n)).payoff p'
        (C.stageGame s (C.bwInd rFin n)).optimalCol := by
  simp only [bwInd, stageValue]
  exact (C.stageGame s (C.bwInd rFin n)).value_row_optimal
end Csg.CSG
