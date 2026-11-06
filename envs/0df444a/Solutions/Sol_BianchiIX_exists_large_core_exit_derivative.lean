-- Prove2me | solution 1 for BianchiIX.exists_large_core_exit_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:11:59.321282+00:00
-- url     : https://prove2.me/submissions/ed3000af-9404-49e5-937f-47e77ca7f0dd

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreRegion_exit_angle_bound
import Theorems.Thm_BianchiIX_exists_coreExit_event
import Theorems.Thm_BianchiIX_exists_large_core_exit_factor
import Theorems.Thm_BianchiIX_exists_large_core_traversal
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
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
open Set Filter
open scoped Topology


/-- Every admissible large-core entrance has an actual moving-exit derivative satisfying (B.38). -/
theorem solution {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let y : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - 1), u, 1, w]
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      0 < coreExitRadialFactor (projectiveOriginalFlow y 0 T) ∧
      coreExitRadialFactor (projectiveOriginalFlow y 0 T) ≤ 1 ∧
      |coreExitRadialFactor (projectiveOriginalFlow y 0 T) - 1| ≤ 8 * (u / k + w ^ 2 / k ^ 2) ∧
      ∃ τ : ProjectiveState → ℝ, τ y = T ∧ ContDiffAt ℝ 1 τ y ∧
        (∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 (τ z) 0 ∧
          projectiveOriginalFlow z 0 (τ z) 2 = 1) ∧
        (∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, T),
          projectiveOriginalFlow z.1 0 z.2 2 = 1 ↔ τ z.1 = z.2) ∧
        ContDiffAt ℝ 1 (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))) y ∧
        ContDiffAt ℝ 1 (fun z => projectiveCoreAngle (projectiveOriginalFlow z 0 (τ z))) y ∧
        ∀ v : ProjectiveState,
          let b := projectiveOriginalFlow y 0 T
          let q := coreProjectedFlowVariation y 0 T v 0
          fderiv ℝ (fun z => projectiveCoreAngle (projectiveOriginalFlow z 0 (τ z))) y v =
            -q / (coreRadius (b 0) (b 2) * (-Real.tanh (projectiveCoreAngle b) +
              coreAngleField (projectiveCoreAngle b) (toCoreAngleState b) 0 / coreRadius (b 0) (b 2))) ∧
          (fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))) y v) 0 =
            coreExitRadialFactor b * q ∧
          |(fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))) y v) 0| ≤ |q| ∧
          |fderiv ℝ (fun z => projectiveCoreAngle (projectiveOriginalFlow z 0 (τ z))) y v| ≤
            2 * |q| / k := by
  intro y
  have hD : 0 < projectiveStateDenom y :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (coreBootstrap_denom_lower hk hu hw)
  have hc : stateConstraint (fromProjectiveState y) = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hcore, hM, _⟩ := exists_large_core_traversal hk hu hw
  obtain ⟨S, _, hfirstS, _, hpos, hle, herr⟩ := exists_large_core_exit_factor hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  have ht : T ∈ normalizedMaxDomain (fromProjectiveState y) 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.le
  have hexit := hcore T ⟨hT.le, le_rfl⟩
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcP, hcZ, hderiv⟩ :=
    exists_coreExit_event hk hD ht hexit.1 hexit.2 hfirst.1.2 hM
  refine ⟨T, hT, hfirst, hpos, hle, herr, τ, hτ, hcτ, hhit, huniq.mono (fun _ h => h.2), hcP, hcZ, ?_⟩
  intro v b q
  have H := hderiv v
  refine ⟨H.1, H.2.1, H.2.2, ?_⟩
  rw [H.1]
  exact coreRegion_exit_angle_bound hk hexit.2 hfirst.1.2 hM q
