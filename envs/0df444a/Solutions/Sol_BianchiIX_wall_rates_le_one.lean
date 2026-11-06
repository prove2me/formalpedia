-- Prove2me | solution 1 for BianchiIX.wall_rates_le_one
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:05:02.584121+00:00
-- url     : https://prove2.me/submissions/aee661b9-b418-46ed-ad67-8f32737961ac

import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BianchiIX
noncomputable section

private theorem BianchiIX.rateOne_eq (p s : ℝ) : rateOne p s = 1 - (p - 1) ^ 2 - s ^ 2 := by
  unfold rateOne shearSq
  ring

private theorem BianchiIX.rateTwo_eq (p s : ℝ) :
    rateTwo p s = 1 - (p + 1 / 2) ^ 2 - (s - Real.sqrt 3 / 2) ^ 2 := by
  have h : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold rateTwo shearSq
  nlinarith

private theorem BianchiIX.rateThree_eq (p s : ℝ) :
    rateThree p s = 1 - (p + 1 / 2) ^ 2 - (s + Real.sqrt 3 / 2) ^ 2 := by
  have h : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold rateThree shearSq
  nlinarith

theorem solution (p s : ℝ) :
    rateOne p s ≤ 1 ∧ rateTwo p s ≤ 1 ∧ rateThree p s ≤ 1 := by
  rw [rateOne_eq, rateTwo_eq, rateThree_eq]
  exact ⟨by nlinarith [sq_nonneg (p - 1), sq_nonneg s],
    by nlinarith [sq_nonneg (p + 1 / 2), sq_nonneg (s - Real.sqrt 3 / 2)],
    by nlinarith [sq_nonneg (p + 1 / 2), sq_nonneg (s + Real.sqrt 3 / 2)]⟩
