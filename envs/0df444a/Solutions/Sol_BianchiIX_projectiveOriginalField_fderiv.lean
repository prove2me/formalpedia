-- Prove2me | solution 1 for BianchiIX.projectiveOriginalField_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:57:29.407125+00:00
-- url     : https://prove2.me/submissions/61326b42-b37d-46c7-ba82-384d82dc6e48

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Theorems.Thm_BianchiIX_contDiff_projectiveField
import Theorems.Thm_BianchiIX_hasFDerivAt_projectiveInverseScale
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


theorem solution {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) (xi : ProjectiveState) :
    fderiv ℝ projectiveOriginalField y xi =
      (6 / projectiveStateDenom y) • fderiv ℝ projectiveField y xi -
      (6 * fderiv ℝ projectiveStateDenom y xi / projectiveStateDenom y ^ 2) • projectiveField y := by
  have hf := ((contDiff_projectiveField 1).differentiable (by norm_num) y).hasFDerivAt
  have hd := (hasFDerivAt_projectiveInverseScale hD).smul hf
  rw [show fderiv ℝ projectiveOriginalField y = _ from hd.fderiv]
  ext i
  change 6 / projectiveStateDenom y * (fderiv ℝ projectiveField y xi) i +
    (-6 / projectiveStateDenom y ^ 2 * fderiv ℝ projectiveStateDenom y xi) * projectiveField y i = _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
