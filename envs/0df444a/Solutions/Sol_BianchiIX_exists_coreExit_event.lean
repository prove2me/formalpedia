-- Prove2me | solution 1 for BianchiIX.exists_coreExit_event
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:07:04.518685+00:00
-- url     : https://prove2.me/submissions/5cdafdd1-6359-4caa-9790-2e563b97e7a9

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Theorems.Thm_BianchiIX_coreRegion_exit_factor_bounds
import Theorems.Thm_BianchiIX_coreRegion_exit_transverse
import Theorems.Thm_BianchiIX_coreWallArrivalDifferential_correction
import Theorems.Thm_BianchiIX_exists_projectiveWall_event
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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreAngle (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n projectiveCoreAngle y := by
  have hv0 := ne_of_gt hv
  unfold projectiveCoreAngle coreAngle
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreRadius (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
  have he : coreEnergy (y 0) (y 2) ≠ 0 := by unfold coreEnergy; positivity
  have he' : (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0 := he
  unfold coreRadius coreEnergy
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_toCoreAngleState (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n toCoreAngleState y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [toCoreAngleState] <;> fun_prop

end
end

theorem solution {k : ℝ} {y : ProjectiveState} {t₀ t : ℝ}
    (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hy : coreRegion k (projectiveOriginalFlow y t₀ t))
    (hV : projectiveOriginalFlow y t₀ t 2 = 1) (hM : projectiveOriginalFlow y t₀ t 0 < 1) :
    ∃ τ : ProjectiveState → ℝ, τ y = t ∧ ContDiffAt ℝ 1 τ y ∧
      (∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) t₀ ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState z) t₀ (τ z) 0 ∧
        projectiveOriginalFlow z t₀ (τ z) 2 = 1) ∧
      (∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, t),
        z.2 ∈ normalizedMaxDomain (fromProjectiveState z.1) t₀ ∧
        (projectiveOriginalFlow z.1 t₀ z.2 2 = 1 ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun z => toCoreAngleState (projectiveOriginalFlow z t₀ (τ z))) y ∧
      ContDiffAt ℝ 1 (fun z => projectiveCoreAngle (projectiveOriginalFlow z t₀ (τ z))) y ∧
      ∀ w : ProjectiveState,
        let b := projectiveOriginalFlow y t₀ t
        let q := coreProjectedFlowVariation y t₀ t w 0
        fderiv ℝ (fun z => projectiveCoreAngle (projectiveOriginalFlow z t₀ (τ z))) y w =
          -q / (coreRadius (b 0) (b 2) * (-Real.tanh (projectiveCoreAngle b) +
            coreAngleField (projectiveCoreAngle b) (toCoreAngleState b) 0 / coreRadius (b 0) (b 2))) ∧
        (fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z t₀ (τ z))) y w) 0 =
          coreExitRadialFactor b * q ∧
        |(fderiv ℝ (fun z => toCoreAngleState (projectiveOriginalFlow z t₀ (τ z))) y w) 0| ≤ |q| := by
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcmap, hdmap⟩ :=
    exists_projectiveWall_event hD ht hA (ne_of_lt (coreRegion_exit_transverse hk hy hV hM).1)
  have hv : 0 < projectiveOriginalFlow y t₀ (τ y) 2 := by rw [hτ, hV]; norm_num
  have hcP := contDiffAt_toCoreAngleState 1 hv
  have hcZ := contDiffAt_projectiveCoreAngle 1 hv
  refine ⟨τ, hτ, hcτ, by simpa only [hV] using hhit, by simpa only [hV] using huniq,
    ?_, ?_, ?_⟩
  · convert! hcP.comp y hcmap using 1
  · convert! hcZ.comp y hcmap using 1
  intro w b q
  have hdP : HasFDerivAt (fun z => toCoreAngleState (projectiveOriginalFlow z t₀ (τ z)))
      ((fderiv ℝ toCoreAngleState b).comp (projectiveWallArrivalDifferential y t₀ t)) y := by
    have H := (hcP.differentiableAt (by norm_num)).hasFDerivAt.comp y hdmap
    rw [hτ] at H
    convert! H using 1
  have hdZ : HasFDerivAt (fun z => projectiveCoreAngle (projectiveOriginalFlow z t₀ (τ z)))
      ((fderiv ℝ projectiveCoreAngle b).comp (projectiveWallArrivalDifferential y t₀ t)) y := by
    have H := (hcZ.differentiableAt (by norm_num)).hasFDerivAt.comp y hdmap
    rw [hτ] at H
    convert! H using 1
  rw [hdP.fderiv, hdZ.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have H := coreWallArrivalDifferential_correction hk hD ht hA hy hV hM w
  refine ⟨H.1, H.2, ?_⟩
  rw [H.2, abs_mul, abs_of_pos (coreRegion_exit_factor_bounds hk hy hV hM).1]
  exact mul_le_of_le_one_left (abs_nonneg _) (coreRegion_exit_factor_bounds hk hy hV hM).2.1
