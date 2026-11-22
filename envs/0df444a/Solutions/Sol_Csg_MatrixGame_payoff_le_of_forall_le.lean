-- Prove2me | solution 1 for Csg.MatrixGame.payoff_le_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:37.45955+00:00
-- url     : https://prove2.me/submissions/207e4b29-8498-44be-9d65-bc5d097e996b

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
    (hy : y ∈ stdSimplex ℝ J) {c : ℝ} (h : ∀ i j, G.A i j ≤ c) :
    G.payoff x y ≤ c := by
  rw [payoff_eq_sum_mul]
  have hinner : ∀ i, ∑ j, G.A i j * y j ≤ c := fun i =>
    calc ∑ j, G.A i j * y j ≤ ∑ j, c * y j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h i j) (hy.1 j)
      _ = c := by rw [← Finset.mul_sum, hy.2, mul_one]
  calc ∑ i, x i * ∑ j, G.A i j * y j ≤ ∑ i, x i * c :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hinner i) (hx.1 i)
    _ = c := by rw [← Finset.sum_mul, hx.2, one_mul]
end Csg.MatrixGame
