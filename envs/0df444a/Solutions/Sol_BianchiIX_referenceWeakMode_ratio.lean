-- Prove2me | solution 1 for BianchiIX.referenceWeakMode_ratio
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:57:07.668654+00:00
-- url     : https://prove2.me/submissions/cf9efbe8-1516-490f-8005-2a3d0659e454

import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
import Theorems.Thm_BianchiIX_referenceTransverseMode_ratio
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


theorem solution (k : ℝ) :
    referenceTransverseMode k 2 (referenceHalfTime k) /
      referenceTransverseMode k 2 (-referenceHalfTime k) =
      Real.exp (-4 * Real.arcosh k / k) := by
  rw [referenceTransverseMode_ratio]
  congr 1
  unfold referenceHalfTime
  ring
