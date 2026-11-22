-- Prove2me | solution 1 for Csg.stageValue_min_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:38:55.800925+00:00
-- url     : https://prove2.me/submissions/6f80f5e9-05d0-4e28-8e23-8f05dd2bb83b

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
theorem _root_.solution (v : SkirmishState → ℝ) (vhide : v .hide = 4 / 5) (vhome : v .home = 1)
    (vwet : v .wet = 0) :
    (skirmishMinCSG.stageGame .hide v).value = 4 / 5 := by
  set G := skirmishMinCSG.stageGame .hide v with hG
  have hA : ∀ a1 a2, G.A a1 a2 = jointR .hide a1 a2 + ∑ s', (jointK .hide a1 a2 s').toReal * v s' :=
    fun a1 a2 => rfl
  have hAhw : G.A .hide .wait = 4 / 5 := by norm_num [hA, jointR, jointExpect_hide_wait, vhide]
  have hAht : G.A .hide .throw = 4 / 5 := by
    norm_num [hA, jointR, jointExpect_hide_throw, vhome, vwet]
  have hAhf : G.A .hide .feint = 1 / 2 := by
    norm_num [hA, jointR, jointExpect_hide_feint, vhome, vwet]
  have hArw : G.A .run .wait = 1 := by norm_num [hA, jointR, jointExpect_run_wait, vhome]
  have hArt : G.A .run .throw = 0 := by norm_num [hA, jointR, jointExpect_run_throw, vwet]
  have hArf : G.A .run .feint = 3 / 10 := by
    norm_num [hA, jointR, jointExpect_run_feint, vhome, vwet]
  apply le_antisymm
  · have hmem : (4 / 5 : ℝ) ∈ G.rowLPFeasible := by
      refine ⟨hiderPureHide, ⟨fun a => by cases a <;> norm_num [hiderPureHide],
        by simp only [hiderAction_sum, hiderPureHide]; norm_num⟩, ?_⟩
      intro j
      simp only [hiderAction_sum]
      cases j <;> norm_num [hiderPureHide, hAhw, hAht, hAhf]
    exact G.value_isLeast_rowLPFeasible.2 hmem
  · have hmem : (4 / 5 : ℝ) ∈ G.colLPFeasible := by
      refine ⟨throwerMinMix, ⟨fun a => by cases a <;> norm_num [throwerMinMix],
        by simp only [throwerAction_sum, throwerMinMix]; norm_num⟩, ?_⟩
      intro i
      simp only [throwerAction_sum]
      cases i <;> norm_num [throwerMinMix, hAhw, hAht, hAhf, hArw, hArt, hArf]
    exact G.value_isGreatest_colLPFeasible.2 hmem
end Csg
