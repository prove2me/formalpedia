-- Prove2me | solution 1 for BianchiIX.coreReturnState_transverse_differential
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:56:04.934677+00:00
-- url     : https://prove2.me/submissions/164c7138-0911-4caf-b41c-da6b0e02aa2a

import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
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
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.coreFlowMultiplier_pos (y : ProjectiveState) (t₀ a b : ℝ) (i : Fin 2) :
    0 < coreFlowMultiplier y t₀ a b i := Real.exp_pos _

end
end

private theorem BianchiIX.coreReturnState_multiplier_formula {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hnear : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1)
    (i : Fin 2) :
    (fun Z => coreReturnState τ Z i.succ) =ᶠ[𝓝 Y]
      (fun Z => Z i.succ * coreReturnMultiplier τ Z i) := by
  filter_upwards [hnear] with Z hZ
  fin_cases i
  · exact hZ.2.1
  · change projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 *
        projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = _
    rw [hZ.1, one_mul, hZ.2.2]
    rfl

/-- Differentiate the actual amplitude product without dividing by an input wall. -/
theorem solution {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hF : DifferentiableAt ℝ (coreReturnState τ) Y)
    (hnear : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 1 = Z 1 * coreReturnMultiplier τ Z 0 ∧
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 3 = Z 2 * coreReturnMultiplier τ Z 1)
    (i : Fin 2) (hlog : DifferentiableAt ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y)
    (v : CoreAngleState) :
    (fderiv ℝ (coreReturnState τ) Y v) i.succ = coreReturnMultiplier τ Y i *
      (v i.succ + Y i.succ * fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y v) := by
  have hm : HasFDerivAt (fun Z => coreReturnMultiplier τ Z i)
      (coreReturnMultiplier τ Y i • fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y) Y := by
    convert! hlog.hasFDerivAt.exp using 1
    · ext Z
      exact (Real.exp_log (coreFlowMultiplier_pos _ _ _ _ i)).symm
    · rw [Real.exp_log (show 0 < coreReturnMultiplier τ Y i from coreFlowMultiplier_pos _ _ _ _ i)]
  have hprod := (hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).mul hm
  change HasFDerivAt (fun Z => Z i.succ * coreReturnMultiplier τ Z i) _ Y at hprod
  have H := congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v)
    ((coreReturnState_multiplier_formula hnear i).fderiv_eq.trans hprod.fderiv)
  rw [fderiv_apply hF i.succ] at H
  convert! H using 1
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring
