-- Prove2me | solution 1 for Csg.MatrixGame.optimalCol_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:40:40.115044+00:00
-- url     : https://prove2.me/submissions/6ac6c23e-ffb4-455c-8a82-60c979d533c5

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
theorem _root_.solution : G.optimalCol ∈ stdSimplex ℝ J := by
  unfold optimalCol
  exact G.exists_optimal_strategies.choose_spec.2.choose_spec.1
end Csg.MatrixGame
