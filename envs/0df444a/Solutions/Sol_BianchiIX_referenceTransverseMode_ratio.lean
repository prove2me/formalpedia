-- Prove2me | solution 1 for BianchiIX.referenceTransverseMode_ratio
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:51:45.346884+00:00
-- url     : https://prove2.me/submissions/85223811-1e4a-43d5-b4cc-1b1bbefed220

import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set


theorem solution (k r h : ℝ) :
    referenceTransverseMode k r h / referenceTransverseMode k r (-h) = Real.exp (-2 * r * h) := by
  unfold referenceTransverseMode
  simp only [mul_neg, Real.cosh_neg]
  rw [mul_div_mul_right _ _ (ne_of_gt (Real.cosh_pos (k * h))), ← Real.exp_sub]
  congr 1
  ring
