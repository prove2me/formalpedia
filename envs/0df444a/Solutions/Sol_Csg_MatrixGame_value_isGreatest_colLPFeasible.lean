-- Prove2me | solution 1 for Csg.MatrixGame.value_isGreatest_colLPFeasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:36:47.727079+00:00
-- url     : https://prove2.me/submissions/af859d5f-42bb-4a77-bb68-eb1cc3cf2f45

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
import Theorems.Thm_Csg_MatrixGame_optimalRow_mem
import Theorems.Thm_Csg_MatrixGame_optimalCol_mem
import Theorems.Thm_Csg_MatrixGame_value_row_optimal
import Theorems.Thm_Csg_MatrixGame_value_col_optimal
import Theorems.Thm_Csg_MatrixGame_payoff_single_left
import Theorems.Thm_Csg_MatrixGame_payoff_ge_of_row_ge

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']
namespace Csg.MatrixGame
theorem _root_.solution : IsGreatest (G.colLPFeasible) G.value := by
  constructor
  · refine ⟨G.optimalCol, G.optimalCol_mem, fun i => ?_⟩
    have h := G.value_row_optimal (Pi.single i 1) (single_mem_stdSimplex ℝ i)
    rwa [payoff_single_left] at h
  · rintro t ⟨q, hq, ht⟩
    calc t ≤ G.payoff G.optimalRow q := G.payoff_ge_of_row_ge q t ht G.optimalRow G.optimalRow_mem
      _ ≤ G.value := G.value_col_optimal q hq
end Csg.MatrixGame
