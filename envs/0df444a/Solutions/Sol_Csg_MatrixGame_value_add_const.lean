-- Prove2me | solution 1 for Csg.MatrixGame.value_add_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:32:27.079814+00:00
-- url     : https://prove2.me/submissions/a74d2881-d799-4fbd-aa35-3a9b134cbe6b

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
import Theorems.Thm_Csg_MatrixGame_optimalRow_mem
import Theorems.Thm_Csg_MatrixGame_optimalCol_mem
import Theorems.Thm_Csg_MatrixGame_value_row_optimal
import Theorems.Thm_Csg_MatrixGame_value_col_optimal
import Theorems.Thm_Csg_MatrixGame_value_unique
import Theorems.Thm_Csg_MatrixGame_payoff_add_const

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
namespace Csg.MatrixGame
theorem _root_.solution {G G' : MatrixGame I J} (c : ℝ) (h : ∀ i j, G'.A i j = G.A i j + c) :
    G'.value = G.value + c := by
  have hpayoff : G'.payoff G.optimalRow G.optimalCol = G.value + c := by
    unfold value
    exact payoff_add_const c h G.optimalRow_mem G.optimalCol_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ I,
      G'.payoff G.optimalRow G.optimalCol ≤ G'.payoff p' G.optimalCol := by
    intro p' hp'
    rw [hpayoff, payoff_add_const c h hp' G.optimalCol_mem]
    linarith [G.value_row_optimal p' hp']
  have hcol : ∀ q' ∈ stdSimplex ℝ J,
      G'.payoff G.optimalRow q' ≤ G'.payoff G.optimalRow G.optimalCol := by
    intro q' hq'
    rw [hpayoff, payoff_add_const c h G.optimalRow_mem hq']
    linarith [G.value_col_optimal q' hq']
  have hunique := G'.value_unique G.optimalRow_mem G.optimalCol_mem hrow hcol
  rw [hpayoff] at hunique
  exact hunique.symm
end Csg.MatrixGame
