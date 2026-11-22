-- Prove2me | solution 1 for Csg.MatrixGame.payoff_relabelRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:08.3817+00:00
-- url     : https://prove2.me/submissions/f65df5eb-a3b3-41ee-a05c-d34ae700433f

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
namespace Csg.MatrixGame
theorem _root_.solution (e : I' ≃ I) (x' : I' → ℝ) (y : J → ℝ) :
    (G.relabelRow e).payoff x' y = G.payoff (x' ∘ ⇑e.symm) y := by
  rw [payoff_eq_sum_mul, payoff_eq_sum_mul,
    ← Equiv.sum_comp e (fun i => (x' ∘ ⇑e.symm) i * ∑ j, G.A i j * y j)]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp only [relabelRow, Function.comp_apply, Equiv.symm_apply_apply]
end Csg.MatrixGame
