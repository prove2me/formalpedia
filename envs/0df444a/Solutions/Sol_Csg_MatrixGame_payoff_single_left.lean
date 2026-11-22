-- Prove2me | solution 1 for Csg.MatrixGame.payoff_single_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:32:49.453133+00:00
-- url     : https://prove2.me/submissions/2e6bd9aa-15a0-487e-b3a6-3cd068501217

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
theorem _root_.solution (i : I) (y : J → ℝ) :
    G.payoff (Pi.single i 1) y = ∑ j, G.A i j * y j := by
  rw [payoff_eq_sum_mul]
  simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq', Finset.mem_univ]
end Csg.MatrixGame
