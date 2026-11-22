-- Prove2me | solution 1 for Csg.MatrixGame.payoff_single_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:32:45.749437+00:00
-- url     : https://prove2.me/submissions/8006f952-8459-4e23-948a-645741d7348c

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
theorem _root_.solution (x : I → ℝ) (j : J) :
    G.payoff x (Pi.single j 1) = ∑ i, x i * G.A i j := by
  rw [payoff_eq_sum_mul']
  simp [Pi.single_apply, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ]
end Csg.MatrixGame
