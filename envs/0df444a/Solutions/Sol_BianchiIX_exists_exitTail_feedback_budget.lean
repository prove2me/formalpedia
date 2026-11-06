-- Prove2me | solution 1 for BianchiIX.exists_exitTail_feedback_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:55:48.114992+00:00
-- url     : https://prove2.me/submissions/15cb0290-9061-406a-b8a3-af7cf7333163

import Definitions.Def_BianchiIX_TerminalConnectionData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

noncomputable section
open BianchiIX
open Set



theorem solution {A D : ℝ} (hA : 1 ≤ A) (hD : 0 ≤ D) :
    ∃ ε > (0 : ℝ), ε ≤ 1 ∧ ∀ T b α K : ℝ,
      0 ≤ T → 0 ≤ b → b * (1 + T) ≤ ε → α * T ≤ K →
      exitTailRateBudget α b A D T ≤ 10 * K + 6 ∧
      20 * (A * b + (A * b) ^ 2 * T) ≤ 40 * A * b := by
  let C := 10 * D + 100 * A + 100 * A ^ 2
  let ε := 1 / (C + 1)
  have hA0 : 0 ≤ A := by linarith only [hA]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 := (div_le_iff₀ (by positivity : 0 < C + 1)).mpr (by linarith only [hC])
  have hCε : C * ε ≤ 1 := by
    dsimp only [ε]
    rw [mul_one_div]
    exact (div_le_iff₀ (by positivity : 0 < C + 1)).mpr (by linarith)
  have hAε : A * ε ≤ 1 := by
    have hAC : A ≤ C := by dsimp only [C]; nlinarith only [hA, hD, sq_nonneg A]
    exact (mul_le_mul_of_nonneg_right hAC hε.le).trans hCε
  refine ⟨ε, hε, hε1, ?_⟩
  intro T b α K hT hb hsmall hα
  have hbε : b ≤ ε := by nlinarith only [hsmall, mul_nonneg hb hT]
  have hbT : b * T ≤ ε := by nlinarith only [hsmall, hb]
  have hb1 : b ≤ 1 := hbε.trans hε1
  have hb2T : b ^ 2 * T ≤ ε := by
    have H := mul_le_mul_of_nonneg_left hb1 (mul_nonneg hb hT)
    nlinarith only [H, hbT]
  have hfeedback : 10 * D * b * T + 100 * A * b + 100 * A ^ 2 * b ^ 2 * T ≤ 1 := by
    have H1 := mul_le_mul_of_nonneg_left hbT (by positivity : 0 ≤ 10 * D)
    have H2 := mul_le_mul_of_nonneg_left hbε (by positivity : 0 ≤ 100 * A)
    have H3 := mul_le_mul_of_nonneg_left hb2T (by positivity : 0 ≤ 100 * A ^ 2)
    dsimp only [C] at hCε
    nlinarith only [H1, H2, H3, hCε]
  have hAbT : A * b * T ≤ 1 := by
    nlinarith only [mul_le_mul_of_nonneg_left hbT hA0, hAε]
  constructor
  · dsimp only [exitTailRateBudget]
    nlinarith only [hfeedback, hα]
  · nlinarith only [mul_le_mul_of_nonneg_left hAbT (mul_nonneg hA0 hb)]
