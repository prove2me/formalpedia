-- Prove2me | solution 1 for Csg.cbStageValue_t2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:56.975802+00:00
-- url     : https://prove2.me/submissions/6fa5c241-8c0b-4ae8-abf4-35d61ff27b62

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_rowMove_sum
import Theorems.Thm_Csg_pointRow_mem
import Theorems.Thm_Csg_pointCol_mem
import Theorems.Thm_Csg_cbT2_payoff
import Theorems.Thm_Csg_MatrixGame_value_unique


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : CBState → ℝ) :
    cbCSG.stageValue .t2 v = min (v .t2) ((v .t1 + v .t3) / 2) := by
  change (cbCSG.stageGame .t2 v).value = min (v .t2) ((v .t1 + v .t3) / 2)
  have hp0 := pointRow_mem .b
  have hp0' := pointRow_mem .d
  have hq0 := pointCol_mem .c
  rcases le_total (v .t2) ((v .t1 + v .t3) / 2) with h | h
  · rw [min_eq_left h]
    have huu : (cbCSG.stageGame .t2 v).payoff (pointRow .b) (pointCol .c) = v .t2 := by
      rw [cbT2_payoff _ _ _ hq0]; simp [pointRow]
    have hrow : ∀ p' ∈ stdSimplex ℝ RowMove,
        (cbCSG.stageGame .t2 v).payoff (pointRow .b) (pointCol .c) ≤
          (cbCSG.stageGame .t2 v).payoff p' (pointCol .c) := by
      intro p' hp'
      rw [huu, cbT2_payoff _ _ _ hq0]
      have hsum : p' .b + p' .d = 1 := by have := hp'.2; rwa [rowMove_sum] at this
      have hb_eq : p' .b = 1 - p' .d := by linarith
      have key : p' .d * v .t2 ≤ p' .d * ((v .t1 + v .t3) / 2) :=
        mul_le_mul_of_nonneg_left h (hp'.1 .d)
      rw [hb_eq]
      nlinarith [key]
    have hcol : ∀ q' ∈ stdSimplex ℝ ColMove,
        (cbCSG.stageGame .t2 v).payoff (pointRow .b) q' ≤
          (cbCSG.stageGame .t2 v).payoff (pointRow .b) (pointCol .c) := by
      intro q' hq'
      rw [huu, cbT2_payoff _ _ _ hq']; simp [pointRow]
    have hval := (cbCSG.stageGame .t2 v).value_unique hp0 hq0 hrow hcol
    rw [← hval]; exact huu
  · rw [min_eq_right h]
    have huu : (cbCSG.stageGame .t2 v).payoff (pointRow .d) (pointCol .c) =
        (v .t1 + v .t3) / 2 := by
      rw [cbT2_payoff _ _ _ hq0]; simp [pointRow]
    have hrow : ∀ p' ∈ stdSimplex ℝ RowMove,
        (cbCSG.stageGame .t2 v).payoff (pointRow .d) (pointCol .c) ≤
          (cbCSG.stageGame .t2 v).payoff p' (pointCol .c) := by
      intro p' hp'
      rw [huu, cbT2_payoff _ _ _ hq0]
      have hsum : p' .b + p' .d = 1 := by have := hp'.2; rwa [rowMove_sum] at this
      have hd_eq : p' .d = 1 - p' .b := by linarith
      have key : p' .b * ((v .t1 + v .t3) / 2) ≤ p' .b * v .t2 :=
        mul_le_mul_of_nonneg_left h (hp'.1 .b)
      rw [hd_eq]
      nlinarith [key]
    have hcol : ∀ q' ∈ stdSimplex ℝ ColMove,
        (cbCSG.stageGame .t2 v).payoff (pointRow .d) q' ≤
          (cbCSG.stageGame .t2 v).payoff (pointRow .d) (pointCol .c) := by
      intro q' hq'
      rw [huu, cbT2_payoff _ _ _ hq']; simp [pointRow]
    have hval := (cbCSG.stageGame .t2 v).value_unique hp0' hq0 hrow hcol
    rw [← hval]; exact huu
end Csg
