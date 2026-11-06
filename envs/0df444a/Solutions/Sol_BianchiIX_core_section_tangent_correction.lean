-- Prove2me | solution 1 for BianchiIX.core_section_tangent_correction
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:55:21.962244+00:00
-- url     : https://prove2.me/submissions/8a30d5e1-8cf9-46dd-b9a1-4617b8c45f1e

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Theorems.Thm_BianchiIX_coreCoordinate_fderiv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

/-- Tangency to a constant active-wall section determines the moving angular endpoint. -/
theorem solution {y : ProjectiveState} (hv : 0 < y 2)
    (hden : -Real.tanh (projectiveCoreAngle y) +
      coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0 / coreRadius (y 0) (y 2) ≠ 0)
    (v : ProjectiveState) (hv2 : v 2 = 0) :
    fderiv ℝ projectiveCoreAngle y v = -(coreClockProjection y v 0) /
        (coreRadius (y 0) (y 2) * (-Real.tanh (projectiveCoreAngle y) +
          coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0 / coreRadius (y 0) (y 2))) ∧
      (fderiv ℝ toCoreAngleState y v) 0 = coreExitRadialFactor y * coreClockProjection y v 0 := by
  let r := coreRadius (y 0) (y 2)
  let c := -Real.tanh (projectiveCoreAngle y)
  let f := coreAngleField (projectiveCoreAngle y) (toCoreAngleState y) 0
  let q := coreClockProjection y v 0
  let dz := fderiv ℝ projectiveCoreAngle y v
  let dr := (fderiv ℝ toCoreAngleState y v) 0
  have hr : r ≠ 0 := ne_of_gt (coreRadius_pos hv)
  have hv0 := ne_of_gt hv
  have hcoord := coreCoordinate_fderiv hv v
  have htangent : dr + r * c * dz = 0 := by
    dsimp only [dr, dz, r, c]
    rw [hcoord.1, hcoord.2, hv2]
    change _ + coreRadius (y 0) (y 2) * (-Real.tanh (coreAngle (y 0) (y 2))) * _ = _
    rw [tanh_coreAngle hv]
    field_simp
    ring
  have hq : q = dr - dz * f := rfl
  have hden' : c + f / r ≠ 0 := hden
  have hz : dz = -q / (r * (c + f / r)) := by
    apply (eq_div_iff (mul_ne_zero hr hden')).mpr
    rw [mul_add, mul_div_cancel₀ f hr]
    nlinarith only [htangent, hq]
  refine ⟨hz, ?_⟩
  change dr = c / (c + f / r) * q
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden').mpr
  rw [mul_add]
  have hrel : r * c * dz = -dr := by linarith only [htangent]
  have hmul := congrArg (fun a : ℝ => a * f / r) hrel
  have he : r * c * dz * f / r = c * dz * f := by field_simp
  rw [he] at hmul
  linear_combination -c * hq + hmul
