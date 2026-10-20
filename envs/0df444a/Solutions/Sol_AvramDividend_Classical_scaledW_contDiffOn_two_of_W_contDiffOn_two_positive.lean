-- Prove2me | solution 1 for AvramDividend.Classical.scaledW_contDiffOn_two_of_W_contDiffOn_two_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T14:22:58.140068+00:00
-- url     : https://prove2.me/submissions/9ebe97cd-e048-4908-ad7f-caf5c23eecd4

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (s : Set ℝ) (hW : ContDiffOn ℝ 2 W s) :
    ContDiffOn ℝ 2
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) s := by
  let k : ℝ := (deriv W a)⁻¹
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hfun :
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) =
        (fun z : ℝ => k * W z) := by
    funext z
    simp [divE, scaleDeriv, ha0, k, div_eq_mul_inv, mul_comm]
  rw [hfun]
  simpa only [smul_eq_mul] using (ContDiffOn.const_smul k hW)
