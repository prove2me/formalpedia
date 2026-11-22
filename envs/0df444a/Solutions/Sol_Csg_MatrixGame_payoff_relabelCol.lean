-- Prove2me | solution 1 for Csg.MatrixGame.payoff_relabelCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:59.887719+00:00
-- url     : https://prove2.me/submissions/9198febd-f6b2-408a-b840-cd2a3e1db494

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
theorem _root_.solution (e : J' ≃ J) (x : I → ℝ) (y' : J' → ℝ) :
    (G.relabelCol e).payoff x y' = G.payoff x (y' ∘ ⇑e.symm) := by
  rw [payoff_eq_sum_mul', payoff_eq_sum_mul',
    ← Equiv.sum_comp e (fun j => (∑ i, x i * G.A i j) * (y' ∘ ⇑e.symm) j)]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp only [relabelCol, Function.comp_apply, Equiv.symm_apply_apply]
end Csg.MatrixGame
