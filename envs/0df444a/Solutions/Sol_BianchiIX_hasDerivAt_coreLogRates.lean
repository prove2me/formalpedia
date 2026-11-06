-- Prove2me | solution 1 for BianchiIX.hasDerivAt_coreLogRates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:28:38.654178+00:00
-- url     : https://prove2.me/submissions/9cb079de-7b6e-407e-8d2a-1af8d66ffc0f

import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
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


theorem solution {γ : ℝ → CoreAngleState} {ξ : CoreAngleState} {z t : ℝ}
    (hγ : HasDerivAt γ ξ t) (hr : γ t 0 ≠ 0) (hd : coreAuxiliary z (γ t) 1 ≠ 0) :
    HasDerivAt (fun s => coreLogRates z (γ s)) ((coreLogRateJacobian z (γ t)).mulVec ξ) t := by
  have hR := hasDerivAt_pi.mp hγ 0
  have hq := hasDerivAt_pi.mp (hasDerivAt_coreAuxiliary (z := z) hγ hr)
  have hrd : γ t 0 * coreAuxiliary z (γ t) 1 ≠ 0 := mul_ne_zero hr hd
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply ((hq 2).div (hq 1) hd).congr_deriv
    simp [coreLogRateJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hd]
    ring
  · apply ((((hq 0).const_add 1).const_mul (-2)).div (hR.mul (hq 1)) hrd).congr_deriv
    simp [coreLogRateJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, hd]
    ring
