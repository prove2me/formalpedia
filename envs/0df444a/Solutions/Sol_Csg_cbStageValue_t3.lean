-- Prove2me | solution 1 for Csg.cbStageValue_t3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:07:38.269849+00:00
-- url     : https://prove2.me/submissions/3bfbea10-1a3e-49db-ad4a-427d5dc8d615

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_colMove_sum
import Theorems.Thm_Csg_pointRow_mem
import Theorems.Thm_Csg_pointCol_mem
import Theorems.Thm_Csg_cbT3_payoff
import Theorems.Thm_Csg_MatrixGame_value_unique


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : CBState → ℝ) :
    cbCSG.stageValue .t3 v = max (v .t3) ((v .t2 + v .t4) / 2) := by
  change (cbCSG.stageGame .t3 v).value = max (v .t3) ((v .t2 + v .t4) / 2)
  have hp0 := pointRow_mem .b
  have hq0 := pointCol_mem .c
  have hq0' := pointCol_mem .d
  rcases le_total (v .t3) ((v .t2 + v .t4) / 2) with h | h
  · rw [max_eq_right h]
    have huu : (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .d) =
        (v .t2 + v .t4) / 2 := by
      rw [cbT3_payoff _ _ _ hp0]; simp [pointCol]
    have hrow : ∀ p' ∈ stdSimplex ℝ RowMove,
        (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .d) ≤
          (cbCSG.stageGame .t3 v).payoff p' (pointCol .d) := by
      intro p' hp'
      rw [huu, cbT3_payoff _ _ _ hp']; simp [pointCol]
    have hcol : ∀ q' ∈ stdSimplex ℝ ColMove,
        (cbCSG.stageGame .t3 v).payoff (pointRow .b) q' ≤
          (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .d) := by
      intro q' hq'
      rw [huu, cbT3_payoff _ _ _ hp0]
      have hsum : q' .c + q' .d = 1 := by have := hq'.2; rwa [colMove_sum] at this
      have hd_eq : q' .d = 1 - q' .c := by linarith
      have key : q' .c * v .t3 ≤ q' .c * ((v .t2 + v .t4) / 2) :=
        mul_le_mul_of_nonneg_left h (hq'.1 .c)
      rw [hd_eq]
      nlinarith [key]
    have hval := (cbCSG.stageGame .t3 v).value_unique hp0 hq0' hrow hcol
    rw [← hval]; exact huu
  · rw [max_eq_left h]
    have huu : (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .c) = v .t3 := by
      rw [cbT3_payoff _ _ _ hp0]; simp [pointCol]
    have hrow : ∀ p' ∈ stdSimplex ℝ RowMove,
        (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .c) ≤
          (cbCSG.stageGame .t3 v).payoff p' (pointCol .c) := by
      intro p' hp'
      rw [huu, cbT3_payoff _ _ _ hp']; simp [pointCol]
    have hcol : ∀ q' ∈ stdSimplex ℝ ColMove,
        (cbCSG.stageGame .t3 v).payoff (pointRow .b) q' ≤
          (cbCSG.stageGame .t3 v).payoff (pointRow .b) (pointCol .c) := by
      intro q' hq'
      rw [huu, cbT3_payoff _ _ _ hp0]
      have hsum : q' .c + q' .d = 1 := by have := hq'.2; rwa [colMove_sum] at this
      have hc_eq : q' .c = 1 - q' .d := by linarith
      have key : q' .d * ((v .t2 + v .t4) / 2) ≤ q' .d * v .t3 :=
        mul_le_mul_of_nonneg_left h (hq'.1 .d)
      rw [hc_eq]
      nlinarith [key]
    have hval := (cbCSG.stageGame .t3 v).value_unique hp0 hq0 hrow hcol
    rw [← hval]; exact huu
end Csg
