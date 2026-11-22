-- Prove2me | solution 1 for Csg.MatrixGame.payoff_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:30.573859+00:00
-- url     : https://prove2.me/submissions/51164997-9849-4f28-8162-288e4246a661

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
theorem _root_.solution {G G' : MatrixGame I J} (h : ∀ i j, G.A i j ≤ G'.A i j) {x : I → ℝ}
    {y : J → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) :
    G.payoff x y ≤ G'.payoff x y := by
  unfold payoff
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h i j) (hx i)) (hy j)
end Csg.MatrixGame
