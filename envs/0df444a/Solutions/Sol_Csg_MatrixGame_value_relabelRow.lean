-- Prove2me | solution 1 for Csg.MatrixGame.value_relabelRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:32:56.625807+00:00
-- url     : https://prove2.me/submissions/710b5bc6-55b7-4ca7-9b78-7122f284bd70

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
import Theorems.Thm_Csg_MatrixGame_optimalRow_mem
import Theorems.Thm_Csg_MatrixGame_optimalCol_mem
import Theorems.Thm_Csg_MatrixGame_value_row_optimal
import Theorems.Thm_Csg_MatrixGame_value_col_optimal
import Theorems.Thm_Csg_MatrixGame_value_unique
import Theorems.Thm_Csg_MatrixGame_mem_stdSimplex_comp_symm
import Theorems.Thm_Csg_MatrixGame_mem_stdSimplex_comp
import Theorems.Thm_Csg_MatrixGame_payoff_relabelRow

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
namespace Csg.MatrixGame
theorem _root_.solution (e : I' ≃ I) : (G.relabelRow e).value = G.value := by
  have hcomp : (fun i' => G.optimalRow (e i')) ∘ ⇑e.symm = G.optimalRow := by
    funext i
    simp
  have hp'_mem : (fun i' => G.optimalRow (e i')) ∈ stdSimplex ℝ I' :=
    mem_stdSimplex_comp e G.optimalRow_mem
  have hpayoff : (G.relabelRow e).payoff (fun i' => G.optimalRow (e i')) G.optimalCol =
      G.value := by
    rw [payoff_relabelRow, hcomp]
    rfl
  have hrow : ∀ p'' ∈ stdSimplex ℝ I', (G.relabelRow e).payoff
      (fun i' => G.optimalRow (e i')) G.optimalCol ≤ (G.relabelRow e).payoff p'' G.optimalCol := by
    intro p'' hp''
    rw [hpayoff, payoff_relabelRow]
    exact G.value_row_optimal _ (mem_stdSimplex_comp_symm e hp'')
  have hcol : ∀ q' ∈ stdSimplex ℝ J, (G.relabelRow e).payoff
      (fun i' => G.optimalRow (e i')) q' ≤
      (G.relabelRow e).payoff (fun i' => G.optimalRow (e i')) G.optimalCol := by
    intro q' hq'
    rw [payoff_relabelRow, hcomp, hpayoff]
    exact G.value_col_optimal q' hq'
  have hval := (G.relabelRow e).value_unique hp'_mem G.optimalCol_mem hrow hcol
  rw [hpayoff] at hval
  exact hval.symm
end Csg.MatrixGame
