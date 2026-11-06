-- Prove2me | solution 1 for BianchiIX.coreWeightedJacobian_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:30:01.087881+00:00
-- url     : https://prove2.me/submissions/88d24e51-705f-401d-aafb-cd01de90e2c3

import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
open BianchiIX


theorem solution {k : ℝ} (hk : k ≠ 0) (z : ℝ)
    (y ξ : CoreAngleState) :
    (coreWeightedJacobian k z y).mulVec (scaleCoreVariation k ξ) =
      scaleCoreVariation k ((coreAngleJacobian z y).mulVec ξ) := by
  ext i
  fin_cases i <;>
    simp [coreWeightedJacobian, scaleCoreVariation, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> field_simp [hk]
