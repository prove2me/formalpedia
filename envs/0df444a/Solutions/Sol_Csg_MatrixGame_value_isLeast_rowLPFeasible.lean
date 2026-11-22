-- Prove2me | solution 1 for Csg.MatrixGame.value_isLeast_rowLPFeasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:36:52.413133+00:00
-- url     : https://prove2.me/submissions/15622d6a-d910-463e-8155-b243c4cdb352

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
import Theorems.Thm_Csg_MatrixGame_optimalRow_mem
import Theorems.Thm_Csg_MatrixGame_optimalCol_mem
import Theorems.Thm_Csg_MatrixGame_value_row_optimal
import Theorems.Thm_Csg_MatrixGame_value_col_optimal
import Theorems.Thm_Csg_MatrixGame_payoff_single_right
import Theorems.Thm_Csg_MatrixGame_payoff_le_of_col_le

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']
namespace Csg.MatrixGame
theorem _root_.solution : IsLeast (G.rowLPFeasible) G.value := by
  constructor
  · refine ⟨G.optimalRow, G.optimalRow_mem, fun j => ?_⟩
    have h := G.value_col_optimal (Pi.single j 1) (single_mem_stdSimplex ℝ j)
    rwa [payoff_single_right] at h
  · rintro t ⟨p, hp, ht⟩
    calc G.value ≤ G.payoff p G.optimalCol := G.value_row_optimal p hp
      _ ≤ t := G.payoff_le_of_col_le p t ht G.optimalCol G.optimalCol_mem
end Csg.MatrixGame
