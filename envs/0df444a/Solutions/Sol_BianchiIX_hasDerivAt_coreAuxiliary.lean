-- Prove2me | solution 1 for BianchiIX.hasDerivAt_coreAuxiliary
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:29:23.802246+00:00
-- url     : https://prove2.me/submissions/89dba98b-d4a5-4baa-9575-07f864936371

import Definitions.Def_BianchiIX_Dynamics_CoreAuxiliary
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
    (hγ : HasDerivAt γ ξ t) (hr : γ t 0 ≠ 0) :
    HasDerivAt (fun s => coreAuxiliary z (γ s)) ((coreAuxiliaryJacobian z (γ t)).mulVec ξ) t := by
  have hR := hasDerivAt_pi.mp hγ 0
  have hU := hasDerivAt_pi.mp hγ 1
  have hP := hasDerivAt_pi.mp hγ 2
  have hV := hR.div_const (Real.cosh z)
  have hv : γ t 0 / Real.cosh z ≠ 0 := div_ne_zero hr (ne_of_gt (Real.cosh_pos z))
  have hr2 : (γ t 0) ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hr' : 2 * γ t 0 ≠ 0 := mul_ne_zero (by norm_num) hr
  have hW : HasDerivAt (fun s => γ s 2 / (γ s 0 / Real.cosh z))
      (-(γ t 2 / (γ t 0 / Real.cosh z)) / γ t 0 * ξ 0 + ξ 2 / (γ t 0 / Real.cosh z)) t := by
    apply (hP.div hV hv).congr_deriv
    field_simp [hr, ne_of_gt (Real.cosh_pos z)]
    ring
  have hC := hU.mul ((hV.add hW).sub hU)
  have hD := (((hU.sub hW).pow 2).div (hR.pow 2) hr2).const_sub 1
  have hA := (((hR.neg.div_const 2).add_const (Real.tanh z)).add (hW.div_const (Real.cosh z))).add
    (((hU.pow 2).sub (hW.pow 2)).div (hR.const_mul 2) hr')
  have hG := hC.neg.sub ((((hU.sub hW).pow 2).const_mul (Real.tanh z)).div hR hr)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply hC.congr_deriv
    simp [coreAuxiliaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, ne_of_gt (Real.cosh_pos z)]
    ring
  · apply hD.congr_deriv
    simp [coreAuxiliaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, ne_of_gt (Real.cosh_pos z)]
    ring
  · apply hA.congr_deriv
    simp [coreAuxiliaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, ne_of_gt (Real.cosh_pos z)]
    ring
  · apply hG.congr_deriv
    simp [coreAuxiliaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp [hr, ne_of_gt (Real.cosh_pos z)]
    ring
