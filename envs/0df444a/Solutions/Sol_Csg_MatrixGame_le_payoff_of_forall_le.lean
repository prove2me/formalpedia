-- Prove2me | solution 1 for Csg.MatrixGame.le_payoff_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:42.546028+00:00
-- url     : https://prove2.me/submissions/87ca6355-3b70-481b-b571-0509b8e23d6e

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
theorem _root_.solution {x : I → ℝ} {y : J → ℝ} (hx : x ∈ stdSimplex ℝ I)
    (hy : y ∈ stdSimplex ℝ J) {c : ℝ} (h : ∀ i j, c ≤ G.A i j) :
    c ≤ G.payoff x y := by
  rw [payoff_eq_sum_mul]
  have hinner : ∀ i, c ≤ ∑ j, G.A i j * y j := fun i =>
    calc c = ∑ j, c * y j := by rw [← Finset.mul_sum, hy.2, mul_one]
      _ ≤ ∑ j, G.A i j * y j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h i j) (hy.1 j)
  calc c = ∑ i, x i * c := by rw [← Finset.sum_mul, hx.2, one_mul]
    _ ≤ ∑ i, x i * ∑ j, G.A i j * y j :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hinner i) (hx.1 i)
end Csg.MatrixGame
