-- Prove2me | solution 1 for BianchiIX.hasFDerivAt_projectiveInverseScale
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:52:51.42454+00:00
-- url     : https://prove2.me/submissions/5a835287-7190-403f-9808-910bda7d413a

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Theorems.Thm_BianchiIX_contDiff_projectiveStateDenom
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
    (hD : projectiveStateDenom y ≠ 0) :
    HasFDerivAt (fun z => 6 / projectiveStateDenom z)
      ((-6 / projectiveStateDenom y ^ 2) • fderiv ℝ projectiveStateDenom y) y := by
  have hd := ((contDiff_projectiveStateDenom 1).differentiable (by norm_num) y).hasFDerivAt
  have hs : HasDerivAt (fun s : ℝ => 6 / s) (-6 / projectiveStateDenom y ^ 2)
      (projectiveStateDenom y) := by
    convert! (hasDerivAt_const (projectiveStateDenom y) (6 : ℝ)).div
      (hasDerivAt_id (projectiveStateDenom y)) hD using 1
    simp
  exact hs.comp_hasFDerivAt y hd
