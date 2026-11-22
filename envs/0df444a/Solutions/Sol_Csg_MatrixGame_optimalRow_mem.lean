-- Prove2me | solution 1 for Csg.MatrixGame.optimalRow_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:40:39.352211+00:00
-- url     : https://prove2.me/submissions/dc23b82b-1275-4bf6-bd36-cf8ff9f8b1a9

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
theorem _root_.solution : G.optimalRow ∈ stdSimplex ℝ I := by
  unfold optimalRow
  exact G.exists_optimal_strategies.choose_spec.1
end Csg.MatrixGame
