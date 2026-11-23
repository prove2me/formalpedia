-- Prove2me | solution 1 for Csg.CSG.bwInd_succ_col_optimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:29:56.542613+00:00
-- url     : https://prove2.me/submissions/62ad58f0-b02c-4f82-b9d3-330610544404

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_BackwardInduction
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_MatrixGame_value_col_optimal

attribute [local simp] Csg.CSG.bwInd_zero

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (rFin : S → ℝ) (n : ℕ) (s : S) :
    ∀ q' ∈ stdSimplex ℝ A2,
      (C.stageGame s (C.bwInd rFin n)).payoff
        (C.stageGame s (C.bwInd rFin n)).optimalRow q' ≤ C.bwInd rFin (n + 1) s := by
  simp only [bwInd, stageValue]
  exact (C.stageGame s (C.bwInd rFin n)).value_col_optimal
end Csg.CSG
