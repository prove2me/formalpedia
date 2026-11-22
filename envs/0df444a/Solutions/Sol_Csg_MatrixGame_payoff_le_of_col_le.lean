-- Prove2me | solution 1 for Csg.MatrixGame.payoff_le_of_col_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:33:23.542739+00:00
-- url     : https://prove2.me/submissions/959d70f3-3f9f-4a39-aed1-457d82f1f5ca

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']
namespace Csg.MatrixGame
theorem _root_.solution (x : I → ℝ) (m : ℝ) (h : ∀ j, (∑ i, x i * G.A i j) ≤ m) :
    ∀ y ∈ stdSimplex ℝ J, G.payoff x y ≤ m := by
  intro y hy
  rw [payoff_eq_sum_mul']
  obtain ⟨hnonneg, hsum⟩ := hy
  calc ∑ j, (∑ i, x i * G.A i j) * y j
      ≤ ∑ j, m * y j := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h j) (hnonneg j)
    _ = m := by rw [← Finset.mul_sum, hsum, mul_one]
end Csg.MatrixGame
