-- Prove2me | solution 1 for Csg.MatrixGame.le_value_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:31:47.158804+00:00
-- url     : https://prove2.me/submissions/7ba80ad1-1dd0-404d-9a40-a72adea8181a

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
import Theorems.Thm_Csg_MatrixGame_optimalRow_mem
import Theorems.Thm_Csg_MatrixGame_optimalCol_mem
import Theorems.Thm_Csg_MatrixGame_le_payoff_of_forall_le

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
namespace Csg.MatrixGame
theorem _root_.solution {c : ℝ} (h : ∀ i j, c ≤ G.A i j) : c ≤ G.value := by
  unfold value
  exact G.le_payoff_of_forall_le G.optimalRow_mem G.optimalCol_mem h
end Csg.MatrixGame
