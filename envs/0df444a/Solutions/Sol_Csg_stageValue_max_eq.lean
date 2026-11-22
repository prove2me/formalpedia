-- Prove2me | solution 1 for Csg.stageValue_max_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:40:36.789699+00:00
-- url     : https://prove2.me/submissions/e1855014-fbbd-4528-a3de-5923bf873e22

import Definitions.Def_Csg_Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_SkirmishFeint
import Theorems.Thm_Csg_hiderAction_sum
import Theorems.Thm_Csg_throwerAction_sum
import Theorems.Thm_Csg_jointExpect_hide_wait
import Theorems.Thm_Csg_jointExpect_hide_throw
import Theorems.Thm_Csg_jointExpect_hide_feint
import Theorems.Thm_Csg_jointExpect_run_wait
import Theorems.Thm_Csg_jointExpect_run_throw
import Theorems.Thm_Csg_jointExpect_run_feint
import Theorems.Thm_Csg_MatrixGame_value_isGreatest_colLPFeasible
import Theorems.Thm_Csg_MatrixGame_value_isLeast_rowLPFeasible


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : SkirmishState → ℝ) (vhide : v .hide = 1 / 2) (vhome : v .home = 1)
    (vwet : v .wet = 0) :
    (skirmishMaxCSG.stageGame .hide v).value = 1 / 2 := by
  set G := skirmishMaxCSG.stageGame .hide v with hG
  have hA : ∀ a2 a1, G.A a2 a1 = jointR .hide a1 a2 + ∑ s', (jointK .hide a1 a2 s').toReal * v s' :=
    fun a2 a1 => rfl
  have hAwh : G.A .wait .hide = 1 / 2 := by norm_num [hA, jointR, jointExpect_hide_wait, vhide]
  have hAwr : G.A .wait .run = 1 := by norm_num [hA, jointR, jointExpect_run_wait, vhome]
  have hAth : G.A .throw .hide = 4 / 5 := by
    norm_num [hA, jointR, jointExpect_hide_throw, vhome, vwet]
  have hAtr : G.A .throw .run = 0 := by norm_num [hA, jointR, jointExpect_run_throw, vwet]
  have hAfh : G.A .feint .hide = 1 / 2 := by
    norm_num [hA, jointR, jointExpect_hide_feint, vhome, vwet]
  have hAfr : G.A .feint .run = 3 / 10 := by
    norm_num [hA, jointR, jointExpect_run_feint, vhome, vwet]
  apply le_antisymm
  · have hmem : (1 / 2 : ℝ) ∈ G.rowLPFeasible := by
      refine ⟨throwerMaxMix, ⟨fun a => by cases a <;> norm_num [throwerMaxMix],
        by simp only [throwerAction_sum, throwerMaxMix]; norm_num⟩, ?_⟩
      intro j
      simp only [throwerAction_sum]
      cases j <;> norm_num [throwerMaxMix, hAwh, hAwr, hAth, hAtr, hAfh, hAfr]
    exact G.value_isLeast_rowLPFeasible.2 hmem
  · have hmem : (1 / 2 : ℝ) ∈ G.colLPFeasible := by
      refine ⟨hiderPureHideCol, ⟨fun a => by cases a <;> norm_num [hiderPureHideCol],
        by simp only [hiderAction_sum, hiderPureHideCol]; norm_num⟩, ?_⟩
      intro i
      simp only [hiderAction_sum]
      cases i <;> norm_num [hiderPureHideCol, hAwh, hAth, hAfh]
    exact G.value_isGreatest_colLPFeasible.2 hmem
end Csg
