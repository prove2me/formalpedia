-- Prove2me | solution 1 for BianchiIX.coreReturn_log_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:06:29.193167+00:00
-- url     : https://prove2.me/submissions/cc931e26-a3b9-454e-a253-68241de5aa1d

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_CoreLogRates
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreLogIntegralVariation
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Theorems.Thm_BianchiIX_contDiffAt_coreOriginalLogRates
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreEntryLogRate_parameter_derivative
import Theorems.Thm_BianchiIX_coreFlow_log_rate_integral_variation
import Theorems.Thm_BianchiIX_coreReturn_angle_derivative
import Theorems.Thm_BianchiIX_fderiv_moving_intervalIntegral
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

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
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveFlowDifferential_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveFlowDifferential y t₀ t₀ = ContinuousLinearMap.id ℝ ProjectiveState := by
  rw [projectiveFlowDifferential, normalizedMaxCurve_initial, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp, projective_chart_differential_inverse hD]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_radius_bounds {k : ℝ} {y : ProjectiveState} (hk : 6 ≤ k) (hy : coreRegion k y) :
    99 / 100 * k ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 101 / 100 * k :=
  coreBootstrap_radius_closed hk (Real.sqrt_nonneg _)
    (by rw [coreRadius_sq]; exact hy.1)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_wall_bounds {k : ℝ} {y : ProjectiveState} (hy : coreRegion k y) :
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧ (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hw0 : 0 ≤ y 3 := (mul_nonneg_iff_of_pos_left hv0).mp hy.2.2.2.1
  exact ⟨hy.2.2.1, hw0, (le_mul_of_one_le_left hw0 hy.2.1).trans hy.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRegion_clock_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    0 < projectiveStateDenom y ∧
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ∧
        0 < coreOriginalClockRate y := by
  have hk0 : 0 < k := by linarith only [hk]
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hD := coreBootstrap_denom_lower (m := y 0) (v := y 2) hk hu hw
  have hd := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
  have hrate := coreBootstrap_original_clock_lower hk hr (zero_le_one.trans hy.2.1) hu hw
  exact ⟨lt_of_lt_of_le (by norm_num) hD, lt_of_lt_of_le (by norm_num) hd,
    lt_of_lt_of_le (one_div_pos.mpr hk0) hrate⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreRadiusEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreRadiusEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreRadiusEntry] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.log_coreFlowMultiplier (y : ProjectiveState) (t₀ a b : ℝ) (i : Fin 2) :
    Real.log (coreFlowMultiplier y t₀ a b i) =
      ∫ t in a..b, coreOriginalLogRates (projectiveOriginalFlow y t₀ t) i :=
  Real.log_exp _

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.contDiffAt_coreRadius_flow {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0) :
    ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ => projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)
      (Y, t) := by
  have he := (contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).comp Y (contDiffAt_coreRadiusEntry 1 hk)
  have hp : ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ =>
      (fromProjectiveState (coreRadiusEntry p.1), p.2)) (Y, t) :=
    (he.comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hf := (normalizedMaxCurve_regular ht).2.comp (Y, t)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (f := fun p : CoreAngleState × ℝ => (fromProjectiveState (coreRadiusEntry p.1), p.2)) hp
  exact (contDiffAt_toProjectiveState 1 (ne_of_gt hA)).comp (Y, t) hf

end
end

private theorem BianchiIX.contDiffAt_coreEntryLogRates {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hV : 0 < projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2)
    (hDz : projectiveStateDenom (projectiveOriginalFlow (coreRadiusEntry Y) 0 t) ≠ 0)
    (hd : let z := projectiveOriginalFlow (coreRadiusEntry Y) 0 t
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0) :
    ContDiffAt ℝ 1 (fun p : CoreAngleState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)) (Y, t) :=
  (contDiffAt_coreOriginalLogRates 1 hV hDz hd).comp (Y, t) (g := coreOriginalLogRates)
    (f := fun p : CoreAngleState × ℝ => projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2)
    (contDiffAt_coreRadius_flow hk hD ht hA)

/-- The interior integrand uses fixed-angle variations; all clock motion is at the endpoints. -/
theorem solution {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (hτ : ContDiffAt ℝ 1 τ Y) (hpos : 0 ≤ τ Y)
    (hdom : Icc 0 (τ Y) ⊆ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : ∀ t ∈ Icc 0 (τ Y), 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ Y), coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t))
    (v : CoreAngleState) (i : Fin 2) :
    let y := coreRadiusEntry Y
    let β := projectiveOriginalFlow y 0
    let w := fderiv ℝ coreRadiusEntry Y v
    let L := fun t => coreLogRates (projectiveCoreAngle (β t)) (toCoreAngleState (β t)) i
    fderiv ℝ (fun Z => Real.log (coreReturnMultiplier τ Z i)) Y v =
      (∫ t in 0..τ Y, coreOriginalClockRate (β t) *
        (fderiv ℝ (coreLogRates (projectiveCoreAngle (β t))) (toCoreAngleState (β t))
          (coreProjectedFlowVariation y 0 t w)) i) +
      L (τ Y) * fderiv ℝ (fun Z => projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z))) Y v -
      L 0 * fderiv ℝ (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) Y v := by
  intro y β w L
  have hV (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) : 0 < β t 2 :=
    lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hreg (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) := coreRegion_clock_regular hk (hcore t ht)
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ Y)) := contDiffAt_pi.mp
    (contDiffAt_coreEntryLogRates (by linarith only [hk]) hD (hdom ht) (hA t ht)
      (hV t ht) (ne_of_gt (hreg t ht).1) (ne_of_gt (hreg t ht).2.1)) i
  have H := fderiv_moving_intervalIntegral hτ hpos hF v
  have hlog : (fun Z => Real.log (coreReturnMultiplier τ Z i)) =
      (fun Z => ∫ t in 0..τ Z, coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry Z) 0 t) i) := by
    ext Z
    exact log_coreFlowMultiplier _ _ _ _ _
  rw [hlog, H]
  have hparam : (∫ t in 0..τ Y, fderiv ℝ (fun p : CoreAngleState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow (coreRadiusEntry p.1) 0 p.2) i) (Y, t) (v, 0)) =
      ∫ t in 0..τ Y, (fderiv ℝ coreOriginalLogRates (β t) (projectiveFlowDifferential y 0 t w)) i := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 (τ Y) := uIcc_of_le hpos ▸ ht
    exact coreEntryLogRate_parameter_derivative (by linarith only [hk]) hD (hdom ht') (hA t ht')
      (hV t ht') (ne_of_gt (hreg t ht').1) (ne_of_gt (hreg t ht').2.1) v i
  rw [hparam, coreFlow_log_rate_integral_variation hk hpos hD hdom hA hcore w i]
  have hend : τ Y ∈ Icc 0 (τ Y) := ⟨hpos, le_rfl⟩
  rw [coreReturn_angle_derivative (by linarith only [hk]) hD (hτ.differentiableAt (by norm_num))
    (hdom hend) (hA _ hend) (hV _ hend) v]
  have hentryAngle := ((contDiffAt_projectiveCoreAngle 1
    (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num)).differentiableAt (by norm_num)).hasFDerivAt.comp Y
      (((contDiffAt_coreRadiusEntry 1 (by linarith only [hk])).differentiableAt (by norm_num)).hasFDerivAt)
  change HasFDerivAt (fun Z => projectiveCoreAngle (coreRadiusEntry Z)) _ _ at hentryAngle
  rw [hentryAngle.fderiv]
  dsimp only [coreLogBoundary, coreOriginalLogRates, ContinuousLinearMap.comp_apply]
  simp only [projectiveOriginalFlow_initial hD, projectiveFlowDifferential_initial hD,
    ContinuousLinearMap.id_apply]
  dsimp only [L, β, y, w]
  simp only [Pi.smul_apply, smul_eq_mul, projectiveOriginalFlow_initial hD]
  ring
