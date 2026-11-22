-- Prove2me | solution 1 for Csg.cbStageValue_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:04:50.809409+00:00
-- url     : https://prove2.me/submissions/25e892d4-1268-4d7c-b438-f786e871e5dc

import Definitions.Def_Csg_CoBuchiOp
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_SafetyCertificate
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_Csg_ConcurrentCoBuchiExample
import Theorems.Thm_Csg_rowMove_sum
import Theorems.Thm_Csg_colMove_sum
import Theorems.Thm_Csg_pointRow_mem
import Theorems.Thm_Csg_pointCol_mem
import Theorems.Thm_Csg_MatrixGame_value_unique


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : CBState → ℝ) (s : CBState) (c : ℝ)
    (hc : ∀ (i : RowMove) (j : ColMove), (cbCSG.stageGame s v).A i j = c) :
    cbCSG.stageValue s v = c := by
  change (cbCSG.stageGame s v).value = c
  have hp0 := pointRow_mem .b
  have hq0 := pointCol_mem .c
  have hpay : ∀ (p : RowMove → ℝ) (q : ColMove → ℝ), p ∈ stdSimplex ℝ RowMove →
      q ∈ stdSimplex ℝ ColMove → (cbCSG.stageGame s v).payoff p q = c := by
    intro p q hp hq
    rw [MatrixGame.payoff_eq_sum_mul, rowMove_sum]
    have h1 : ∑ j, (cbCSG.stageGame s v).A .b j * q j = c := by
      have : ∀ j, (cbCSG.stageGame s v).A .b j * q j = c * q j := fun j => by
        rw [hc .b j]
      rw [colMove_sum, this .c, this .d, ← mul_add, ← colMove_sum q, hq.2, mul_one]
    have h2 : ∑ j, (cbCSG.stageGame s v).A .d j * q j = c := by
      have : ∀ j, (cbCSG.stageGame s v).A .d j * q j = c * q j := fun j => by
        rw [hc .d j]
      rw [colMove_sum, this .c, this .d, ← mul_add, ← colMove_sum q, hq.2, mul_one]
    have hsum : p .b + p .d = 1 := by have := hp.2; rwa [rowMove_sum] at this
    rw [h1, h2, ← add_mul, hsum, one_mul]
  have huu := hpay _ _ hp0 hq0
  have hrow : ∀ p' ∈ stdSimplex ℝ RowMove,
      (cbCSG.stageGame s v).payoff (pointRow .b) (pointCol .c) ≤
        (cbCSG.stageGame s v).payoff p' (pointCol .c) := fun p' hp' =>
    le_of_eq (huu.trans (hpay p' _ hp' hq0).symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ ColMove,
      (cbCSG.stageGame s v).payoff (pointRow .b) q' ≤
        (cbCSG.stageGame s v).payoff (pointRow .b) (pointCol .c) := fun q' hq' =>
    le_of_eq ((hpay _ q' hp0 hq').trans huu.symm)
  have hval := (cbCSG.stageGame s v).value_unique hp0 hq0 hrow hcol
  rw [← hval]; exact huu
end Csg
