-- Prove2me | solution 1 for Csg.MatrixGame.value_row_optimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:42:17.067205+00:00
-- url     : https://prove2.me/submissions/cc1977e3-3f80-47f9-9de9-bea641b86d84

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
namespace Csg.MatrixGame
theorem _root_.solution : ∀ p' ∈ stdSimplex ℝ I, G.value ≤ G.payoff p' G.optimalCol := by
  unfold value
  exact G.exists_optimal_strategies.choose_spec.2.choose_spec.2.1
end Csg.MatrixGame
