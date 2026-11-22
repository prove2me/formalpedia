-- Prove2me | solution 1 for Csg.MatrixGame.payoff_add_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:56.526804+00:00
-- url     : https://prove2.me/submissions/c3a12ed8-66d4-4d6a-9d36-92cd4f02178c

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
theorem _root_.solution {G G' : MatrixGame I J} (c : ℝ) (h : ∀ i j, G'.A i j = G.A i j + c)
    {x : I → ℝ} {y : J → ℝ} (hx : x ∈ stdSimplex ℝ I) (hy : y ∈ stdSimplex ℝ J) :
    G'.payoff x y = G.payoff x y + c := by
  rw [payoff_eq_sum_mul, payoff_eq_sum_mul]
  have hinner : ∀ i, ∑ j, G'.A i j * y j = (∑ j, G.A i j * y j) + c := by
    intro i
    calc ∑ j, G'.A i j * y j = ∑ j, (G.A i j * y j + c * y j) :=
          Finset.sum_congr rfl fun j _ => by rw [h i j]; ring
      _ = (∑ j, G.A i j * y j) + ∑ j, c * y j := Finset.sum_add_distrib
      _ = (∑ j, G.A i j * y j) + c := by rw [← Finset.mul_sum, hy.2, mul_one]
  calc ∑ i, x i * ∑ j, G'.A i j * y j
      = ∑ i, x i * ((∑ j, G.A i j * y j) + c) :=
        Finset.sum_congr rfl fun i _ => by rw [hinner i]
    _ = ∑ i, (x i * ∑ j, G.A i j * y j + x i * c) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = (∑ i, x i * ∑ j, G.A i j * y j) + ∑ i, x i * c := Finset.sum_add_distrib
    _ = (∑ i, x i * ∑ j, G.A i j * y j) + c := by rw [← Finset.sum_mul, hx.2, one_mul]
end Csg.MatrixGame
