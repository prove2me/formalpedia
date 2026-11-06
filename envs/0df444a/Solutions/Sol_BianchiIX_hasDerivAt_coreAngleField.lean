-- Prove2me | solution 1 for BianchiIX.hasDerivAt_coreAngleField
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:40:01.846788+00:00
-- url     : https://prove2.me/submissions/b1aefeb8-0b63-4cba-947f-f0da434144fe

import Definitions.Def_BianchiIX_Dynamics_CoreLinearization
import Theorems.Thm_BianchiIX_hasDerivAt_coreAuxiliary
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

private theorem BianchiIX.coreAngleField_auxiliary (z : ℝ) (y : CoreAngleState) :
    coreAngleField z y = ![(coreAuxiliary z y) 3 / (coreAuxiliary z y) 1,
      y 1 * (coreAuxiliary z y) 2 / (coreAuxiliary z y) 1,
      -2 * y 2 * (1 + (coreAuxiliary z y) 0) / (y 0 * (coreAuxiliary z y) 1)] := rfl

theorem solution {γ : ℝ → CoreAngleState} {ξ : CoreAngleState} {z t : ℝ}
    (hγ : HasDerivAt γ ξ t) (hr : γ t 0 ≠ 0) (hd : (coreAuxiliary z (γ t)) 1 ≠ 0) :
    HasDerivAt (fun s => coreAngleField z (γ s)) ((coreAngleJacobian z (γ t)).mulVec ξ) t := by
  have hR := hasDerivAt_pi.mp hγ 0
  have hU := hasDerivAt_pi.mp hγ 1
  have hP := hasDerivAt_pi.mp hγ 2
  have hq := hasDerivAt_pi.mp (hasDerivAt_coreAuxiliary (z := z) hγ hr)
  have hrd : γ t 0 * (coreAuxiliary z (γ t)) 1 ≠ 0 := mul_ne_zero hr hd
  apply hasDerivAt_pi.mpr
  intro i
  simp_rw [coreAngleField_auxiliary]
  fin_cases i
  · apply ((hq 3).div (hq 1) hd).congr_deriv
    simp [coreAngleJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hd]
    ring
  · apply ((hU.mul (hq 2)).div (hq 1) hd).congr_deriv
    simp [coreAngleJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hd]
    ring
  · apply (((hP.const_mul (-2)).mul ((hq 0).const_add 1)).div (hR.mul (hq 1)) hrd).congr_deriv
    simp [coreAngleJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, hd]
    ring
