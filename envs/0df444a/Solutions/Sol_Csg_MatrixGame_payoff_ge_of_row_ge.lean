-- Prove2me | solution 1 for Csg.MatrixGame.payoff_ge_of_row_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:33:18.023996+00:00
-- url     : https://prove2.me/submissions/b4c44b13-c861-4d65-8738-f4fcdfc787cb

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
theorem _root_.solution (y : J → ℝ) (m : ℝ) (h : ∀ i, m ≤ ∑ j, G.A i j * y j) :
    ∀ x ∈ stdSimplex ℝ I, m ≤ G.payoff x y := by
  intro x hx
  rw [payoff_eq_sum_mul]
  obtain ⟨hnonneg, hsum⟩ := hx
  calc m = m * ∑ i, x i := by rw [hsum, mul_one]
    _ = ∑ i, m * x i := by rw [Finset.mul_sum]
    _ ≤ ∑ i, x i * ∑ j, G.A i j * y j := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_comm m (x i)]
        exact mul_le_mul_of_nonneg_left (h i) (hnonneg i)
end Csg.MatrixGame
