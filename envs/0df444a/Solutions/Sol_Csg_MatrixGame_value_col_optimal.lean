-- Prove2me | solution 1 for Csg.MatrixGame.value_col_optimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:42:25.385381+00:00
-- url     : https://prove2.me/submissions/b42beb96-fccc-445b-9828-df7f3a0bbc1d

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
theorem _root_.solution : ∀ q' ∈ stdSimplex ℝ J, G.payoff G.optimalRow q' ≤ G.value := by
  unfold value
  exact G.exists_optimal_strategies.choose_spec.2.choose_spec.2.2
end Csg.MatrixGame
