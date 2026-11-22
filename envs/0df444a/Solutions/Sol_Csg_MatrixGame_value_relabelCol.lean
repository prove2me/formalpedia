-- Prove2me | solution 1 for Csg.MatrixGame.value_relabelCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:34:33.624213+00:00
-- url     : https://prove2.me/submissions/7a8ef113-4ea6-4bc7-9162-ed74e5e82aeb

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
import Theorems.Thm_Csg_MatrixGame_optimalRow_mem
import Theorems.Thm_Csg_MatrixGame_optimalCol_mem
import Theorems.Thm_Csg_MatrixGame_value_row_optimal
import Theorems.Thm_Csg_MatrixGame_value_col_optimal
import Theorems.Thm_Csg_MatrixGame_value_unique
import Theorems.Thm_P2M_Csg_MatrixGame_mem_stdSimplex_comp_symm__e48fc2146e7d
import Theorems.Thm_P2M_Csg_MatrixGame_mem_stdSimplex_comp__eaf65fcbba18
import Theorems.Thm_Csg_MatrixGame_payoff_relabelCol

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']
namespace Csg.MatrixGame
theorem _root_.solution (e : J' ≃ J) : (G.relabelCol e).value = G.value := by
  have hcomp : (fun j' => G.optimalCol (e j')) ∘ ⇑e.symm = G.optimalCol := by
    funext j
    simp
  have hq'_mem : (fun j' => G.optimalCol (e j')) ∈ stdSimplex ℝ J' :=
    mem_stdSimplex_comp' e G.optimalCol_mem
  have hpayoff : (G.relabelCol e).payoff G.optimalRow (fun j' => G.optimalCol (e j')) =
      G.value := by
    rw [payoff_relabelCol, hcomp]
    rfl
  have hrow : ∀ p' ∈ stdSimplex ℝ I, (G.relabelCol e).payoff
      G.optimalRow (fun j' => G.optimalCol (e j')) ≤
      (G.relabelCol e).payoff p' (fun j' => G.optimalCol (e j')) := by
    intro p' hp'
    rw [hpayoff, payoff_relabelCol, hcomp]
    exact G.value_row_optimal p' hp'
  have hcol : ∀ q'' ∈ stdSimplex ℝ J', (G.relabelCol e).payoff G.optimalRow q'' ≤
      (G.relabelCol e).payoff G.optimalRow (fun j' => G.optimalCol (e j')) := by
    intro q'' hq''
    rw [hpayoff, payoff_relabelCol]
    exact G.value_col_optimal _ (mem_stdSimplex_comp_symm' e hq'')
  have hval := (G.relabelCol e).value_unique G.optimalRow_mem hq'_mem hrow hcol
  rw [hpayoff] at hval
  exact hval.symm
end Csg.MatrixGame
