-- Prove2me | solution 1 for BianchiIX.exists_actual_entrance_phase_response
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:19:24.730323+00:00
-- url     : https://prove2.me/submissions/ce4c67e1-d01e-4239-9b09-d5bdd7f3f415

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_FlowComposition
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_projectiveOriginalField
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_contDiff_projectiveField
import Theorems.Thm_BianchiIX_contDiff_projectiveStateDenom
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_coupled_clock_variation_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_entranceWallLogRates_weighted_bounds
import Theorems.Thm_BianchiIX_exists_scaled_entrance_phase_feedback_budget
import Theorems.Thm_BianchiIX_exists_scaled_entrance_phase_source_budget
import Theorems.Thm_BianchiIX_exists_scaled_entrance_wall_solution_growth
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_coordinate_clock_variation
import Theorems.Thm_BianchiIX_hasDerivAt_coordinate_variation
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_hasFDerivAt_stableBoundaryProjection_in_band
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_integral_le_of_exp_decay
import Theorems.Thm_BianchiIX_mem_normalizedMaxDomain_retime
import Theorems.Thm_BianchiIX_norm_le_exp_of_signedRowSum
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_stable_global_region
import Theorems.Thm_BianchiIX_normalized_stable_limit
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_scaled_stable_boundary_drift
import Theorems.Thm_BianchiIX_stableRescaledDifferential_stable_decay
import Theorems.Thm_BianchiIX_stableRescaledJacobian_center_bounds
import Theorems.Thm_BianchiIX_toProjectiveState_denom_pos
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_phase_feedback_small {F ε k θ u v w : ℝ}
    (hF : 0 < F) (hε : ε ≤ 1) (hsmall : ε ≤ 1 / (4 * F)) (hk : 1 ≤ k)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hu : 0 ≤ u ∧ u ≤ ε)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ ε) :
    0 ≤ F * (u * v + θ * (v * w) ^ 2) / k ^ 2 ∧
      F * (u * v + θ * (v * w) ^ 2) / k ^ 2 ≤ 1 / 2 := by
  have hu0 := hu.1
  have hv0 := hv.1
  have hw0 := hw.1
  have hθ0 := hθ.1
  have hP : u * v ≤ ε := (mul_le_of_le_one_right hu.1 hv.2).trans hu.2
  have hW : v * w ≤ w := mul_le_of_le_one_left hw.1 hv.2
  have hW0 : 0 ≤ v * w := mul_nonneg hv.1 hw.1
  have hW1 : v * w ≤ 1 := hW.trans (hw.2.trans hε)
  have hW2 : (v * w) ^ 2 ≤ w := by
    nlinarith only [mul_le_mul_of_nonneg_left hW1 hW0, hW]
  have hS : θ * (v * w) ^ 2 ≤ ε :=
    ((mul_le_of_le_one_left (sq_nonneg _) hθ.2).trans hW2).trans hw.2
  have H : 4 * F * ε ≤ 1 := by
    have := (le_div_iff₀ (show 0 < 4 * F by positivity)).mp hsmall
    nlinarith only [this]
  constructor
  · positivity
  · calc
      _ ≤ F * (u * v + θ * (v * w) ^ 2) := div_le_self (by positivity) (one_le_pow₀ hk)
      _ ≤ F * (2 * ε) := mul_le_mul_of_nonneg_left (by linarith only [hP, hS]) hF.le
      _ ≤ 1 / 2 := by nlinarith only [H]

end
end

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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_scaled_observable_variation
    {p : E → F} {f : E → E} {Y v : ℝ → E} {t a : ℝ}
    (hp : ContDiffAt ℝ 2 p (Y t)) (hf : DifferentiableAt ℝ f (Y t))
    (hY : HasDerivAt Y (a • f (Y t)) t)
    (hv : HasDerivAt v (a • fderiv ℝ f (Y t) (v t)) t) :
    HasDerivAt (fun s => fderiv ℝ p (Y s) (v s))
      (a • fderiv ℝ (fun x => fderiv ℝ p x (f x)) (Y t) (v t)) t := by
  have hdp : DifferentiableAt ℝ (fderiv ℝ p) (Y t) :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hLie := hdp.hasFDerivAt.clm_apply hf.hasFDerivAt
  have hsym := (hp.isSymmSndFDerivAt (by norm_num)).eq (f (Y t)) (v t)
  have hd := (hdp.hasFDerivAt.comp_hasDerivAt t hY).clm_apply hv
  convert! hd using 1
  rw [hLie.fderiv]
  change a • (fderiv ℝ p (Y t) (fderiv ℝ f (Y t) (v t)) +
      fderiv ℝ (fderiv ℝ p) (Y t) (v t) (f (Y t))) = _
  simp only [map_smul, smul_apply, smul_add, Function.comp_apply]
  rw [hsym]
  module

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_field (m u w : ℝ) :
    phaseVelocity m u 0 w = m * u ^ 2 - (m + 1) * u * w + w ^ 2 ∧
    strongVelocity m u 0 w = stableStrongRate m u w * u ∧
    activeVelocity m u 0 w = 0 ∧
    weakVelocity m u 0 w = stableWeakRate m u w * w := by
  unfold phaseVelocity strongVelocity activeVelocity weakVelocity coupling
    stableStrongRate stableWeakRate
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_band {m c : ℝ} (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10) :
    3 ≤ c + 1 ∧ 5 / 8 * (c + 1) ≤ m ∧ 0 ≤ m ∧ m ≤ c + 1 ∧
      0 ≤ m + 1 ∧ m + 1 ≤ 2 * (c + 1) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hm
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_rates {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10)
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1 / 100) :
    stableStrongRate m u w / (c + 1) ≤ -(c + 1) / 8 ∧
      stableWeakRate m u w / (c + 1) ≤ -(1 / 4) := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hK0 : 0 < c + 1 := by linarith
  have hu2 : u ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := sq_le_sq.mpr (by norm_num; exact hu)
  have huw : |u * w| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  constructor
  · apply (div_le_iff₀ hK0).mpr
    unfold stableStrongRate
    nlinarith [sq_nonneg w, sq_nonneg (c + 1 - 3)]
  · apply (div_le_iff₀ hK0).mpr
    unfold stableWeakRate
    nlinarith [(abs_le.mp huw).1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_denom {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10)
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1 / 100) :
    0 < projectiveDenom m u 0 w ∧ projectiveDenom m u 0 w ≤ 2 * (c + 1) ^ 2 := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have heq : projectiveDenom m u 0 w = 3 + m ^ 2 + (u - w) ^ 2 := by
    unfold projectiveDenom curvature
    ring
  rw [heq]
  have hd : |u - w| ≤ 1 / 50 := (abs_sub _ _).trans (by linarith)
  have hd2 : (u - w) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := sq_le_sq.mpr (by norm_num; exact hd)
  have hm2 := (sq_le_sq₀ hm0 (by linarith : 0 ≤ c + 1)).mpr hmK
  constructor
  · positivity
  · nlinarith [sq_nonneg (c + 1 - 3)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_speed_bounds {k m u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hm : 4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    3 / 4 * k ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ 21 / 20 * k := by
  have hC := connection_coupling_bounds hu.1 hv ⟨hw.1, by linarith [hw.2]⟩
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hm.1, hm.2, hC.1, hC.2, hu.2, hu2, hk]

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_retime {x : NormalizedState} {t₀ t₁ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₁) :
    normalizedMaxCurve x t₁ t = normalizedMaxCurve x t₀ (t + t₀ - t₁) :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).retime t₁)
    (mem_normalizedMaxDomain_retime.mp ht)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_rebase {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (normalizedMaxCurve x t₀ s) s t = normalizedMaxCurve x t₀ t :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).rebase hs) ht

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

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
open Set Filter Metric
open scoped Topology ContDiff

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_smooth {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ ∞ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  contDiffAt_infty.mpr (fun n => contDiffAt_normalizedMaxCurve_nat n ht)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_two {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  (contDiffAt_normalizedMaxCurve_smooth ht).of_le (by decide)

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

private theorem BianchiIX.hasFDerivAt_projectiveOriginalFlow_initial {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasFDerivAt (fun z => projectiveOriginalFlow z t₀ t) (projectiveFlowDifferential y t₀ t) y := by
  have hfrom := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).differentiableAt (by norm_num)).hasFDerivAt
  have hto := ((contDiffAt_toProjectiveState 1 (ne_of_gt hA)).differentiableAt (by norm_num)).hasFDerivAt
  exact hto.comp y ((hasFDerivAt_normalizedMaxCurve_initial ht).comp y hfrom)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_projectiveOriginalFlow_time {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasDerivAt (projectiveOriginalFlow y t₀)
      (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_projectiveOriginalFlow (hasDerivAt_normalizedMaxCurve ht) (ne_of_gt hA) hc

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_projectiveOriginalFlow_two {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2) (y, t) := by
  have hparam : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2)) (y, t) :=
    ((contDiffAt_fromProjectiveState 2 (ne_of_gt hD)).comp (y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hN : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2) (y, t) := by
    simpa only [Function.comp_def] using (contDiffAt_normalizedMaxCurve_two ht).comp (y, t) hparam
  simpa only [Function.comp_def, projectiveOriginalFlow] using
    (contDiffAt_toProjectiveState 2 (ne_of_gt hA)).comp (y, t) hN

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.abs_le_exp_of_clock_damping {f d z z' : ℝ → ℝ} {a b c : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (z' t * (d t * f t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzpos : ∀ t ∈ Icc a b, 0 ≤ z' t)
    (hd : ∀ t ∈ Icc a b, d t ≤ -c) :
    ∀ t ∈ Icc a b, |f t| ≤ |f a| * Real.exp (-c * (z t - z a)) := by
  have H := abs_le_affine_exp_of_clock_damping (g := fun _ => 0) (B := 0)
    (by simpa only [add_zero] using hf) hz hzpos hd (by simp)
  simpa only [zero_mul, mul_zero, add_zero, mul_comm] using H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.scaled_stable_boundary_decay {Y : ℝ → ProjectiveState} {a z : ℝ → ℝ}
    {s t c : ℝ} (hc : 2 ≤ c)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hz : ∀ r ∈ Icc s t, HasDerivAt z ((c + 1) * a r) r)
    (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hv : ∀ r ∈ Icc s t, Y r 2 = 0)
    (hm : ∀ r ∈ Icc s t, |Y r 0 - c| ≤ 1 / 10)
    (hu : ∀ r ∈ Icc s t, |Y r 1| ≤ 1 / 100)
    (hw : ∀ r ∈ Icc s t, |Y r 3| ≤ 1 / 100) :
    ∀ r ∈ Icc s t,
      |Y r 1| ≤ |Y s 1| * Real.exp (-(c + 1) / 8 * (z r - z s)) ∧
      |Y r 3| ≤ |Y s 3| * Real.exp (-(1 / 4) * (z r - z s)) := by
  have hK : 0 < c + 1 := by linarith
  have hcoord (i : Fin 4) (r : ℝ) (hr : r ∈ Icc s t) := hasDerivAt_pi.mp (hY r hr) i
  have hU (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun q => Y q 1)
        (((c + 1) * a r) * (stableStrongRate (Y r 0) (Y r 1) (Y r 3) / (c + 1) * Y r 1)) r := by
    convert! hcoord 1 r hr using 1
    change _ = a r * strongVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    rw [hv r hr, (stable_boundary_field (Y r 0) (Y r 1) (Y r 3)).2.1]
    field_simp
  have hW (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun q => Y q 3)
        (((c + 1) * a r) * (stableWeakRate (Y r 0) (Y r 1) (Y r 3) / (c + 1) * Y r 3)) r := by
    convert! hcoord 3 r hr using 1
    change _ = a r * weakVelocity (Y r 0) (Y r 1) (Y r 2) (Y r 3)
    rw [hv r hr, (stable_boundary_field (Y r 0) (Y r 1) (Y r 3)).2.2.2]
    field_simp
  have H := abs_le_exp_of_clock_damping hU hz (fun r hr => mul_nonneg hK.le (ha r hr))
    (fun r hr => by simpa only [neg_div] using (stable_boundary_rates hc (hm r hr) (hu r hr) (hw r hr)).1)
  have J := abs_le_exp_of_clock_damping hW hz (fun r hr => mul_nonneg hK.le (ha r hr))
    (fun r hr => (stable_boundary_rates hc (hm r hr) (hu r hr) (hw r hr)).2)
  intro r hr
  exact ⟨by simpa only [neg_div] using H r hr, J r hr⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.hasDerivAt_normalizedStableClock {x : NormalizedState} {t₀ s c t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (normalizedStableClock x t₀ s c)
      ((c + 1) * normalizedProjectiveRate x t₀ t) t :=
  ((hasStrictDerivAt_integralClock (convex_normalizedMaxDomain x t₀)
    (isOpen_normalizedMaxDomain x t₀) (continuousOn_normalizedProjectiveRate x t₀) hs ht).hasDerivAt).const_mul _

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.normalized_stable_prefix_estimates {x : NormalizedState} {t₀ s t c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r)
    (hy : ∀ r ∈ Icc s t, stableBoundaryRegion c (toProjectiveState (normalizedMaxCurve x t₀ r))) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    |Y t 0 - Y s 0| ≤ 8 * (|Y s 1| + |Y s 3|) ^ 2 / (c + 1) ∧
    (∀ r ∈ Icc s t,
      |Y r 1| ≤ |Y s 1| * Real.exp (-(c + 1) / 8 * normalizedStableClock x t₀ s c r) ∧
      |Y r 3| ≤ |Y s 3| * Real.exp (-(1 / 4) * normalizedStableClock x t₀ s c r)) ∧
    (∀ r ∈ Icc s t, |Y r 1| ≤ |Y s 1| ∧ |Y r 3| ≤ |Y s 3|) := by
  intro Y
  have hdom (r : ℝ) (hr : s ≤ r) : r ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hx t₀ (hs.trans hr)
  have hY (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt Y (normalizedProjectiveRate x t₀ r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hx (hs.trans hr.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA r hr)) H.2.1
  have hz (r : ℝ) (hr : r ∈ Icc s t) :=
    hasDerivAt_normalizedStableClock (c := c) (hdom s le_rfl) (hdom r hr.1)
  have hac : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono (fun r hr => hdom r hr.1)
  have H := scaled_stable_boundary_decay hc hY hz (fun r hr => (hA r hr).le)
    (fun r hr => (hy r hr).2.2.1) (fun r hr => (hy r hr).1)
    (fun r hr => (hy r hr).2.1) (fun r hr => (hy r hr).2.2.2)
  have hzero : normalizedStableClock x t₀ s c s = 0 := by
    simp [normalizedStableClock, integralClock_initial]
  simp only [hzero, sub_zero] at H
  refine ⟨scaled_stable_boundary_drift hst hc hY hz hac (fun r hr => (hA r hr).le)
    (fun r hr => (hy r hr).2.2.1) (fun r hr => (hy r hr).1)
    (fun r hr => (hy r hr).2.1) (fun r hr => (hy r hr).2.2.2), H, ?_⟩
  intro r hr
  have hz0 : 0 ≤ normalizedStableClock x t₀ s c r := by
    apply mul_nonneg (by linarith : 0 ≤ c + 1)
    apply intervalIntegral.integral_nonneg hr.1
    intro q hq
    exact (hA q ⟨hq.1, hq.2.trans hr.2⟩).le
  constructor
  · exact (H r hr).1.trans (mul_le_of_le_one_right (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hz0)))
  · exact (H r hr).2.trans (mul_le_of_le_one_right (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (by linarith)))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.continuous_entranceClockRate : Continuous entranceClockRate := by
  unfold entranceClockRate connectionSpeed coupling
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_phase {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    4 / 5 * k ≤ y 0 - 1 ∧ y 0 - 1 ≤ 101 / 100 * k :=
  entrance_phase_bounds hk hy.1 hy.2.1 hy.2.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_speed {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    3 / 4 * k ≤ entranceClockRate y ∧ entranceClockRate y ≤ 21 / 20 * k :=
  entrance_speed_bounds hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_clock_pos {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    0 < entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_entranceLog_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hv : Y t 2 ≠ 0) :
    HasDerivAt (fun s => Real.log (Y s 2)) (a * entranceClockRate (Y t)) t := by
  convert! (hasDerivAt_pi.mp hY 2).log hv using 1
  change _ = (a * activeVelocity (Y t 0) (Y t 1) (Y t 2) (Y t 3)) / Y t 2
  unfold activeVelocity entranceClockRate connectionSpeed
  field_simp

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.normalizedStableClock_lower {x : NormalizedState} {t₀ s t c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate x t₀ r) :
    3 / (c + 1) * (t - s) ≤ normalizedStableClock x t₀ s c t := by
  have hK : 0 < c + 1 := by linarith
  have hcA : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono
      (fun r hr => normalizedMaxDomain_contains_Ici_of_constraint hx t₀ (hs.trans hr.1))
  have H := intervalIntegral.integral_mono_on (μ := volume) hst (intervalIntegrable_const (c := 3 / (c + 1) ^ 2))
    (hcA.intervalIntegrable_of_Icc hst) hA
  rw [intervalIntegral.integral_const] at H
  have H' := mul_le_mul_of_nonneg_left H hK.le
  convert! H' using 1
  simp only [smul_eq_mul]
  field_simp

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryEntry_denom_pos (m u w : ℝ) :
    0 < projectiveStateDenom (stableBoundaryEntry m u w) := by
  change 0 < projectiveDenom m u 0 w
  have H : projectiveDenom m u 0 w = 3 + m ^ 2 + (u - w) ^ 2 := by
    unfold projectiveDenom curvature
    ring
  rw [H]
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_initial (m u w : ℝ) :
    stableBoundaryOrbit m u w 0 = stableBoundaryEntry m u w := by
  unfold stableBoundaryOrbit
  rw [normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (stableBoundaryEntry_denom_pos m u w))

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_global {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    ∀ t ≥ 0,
      3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 t ∧
      stableBoundaryRegion c (stableBoundaryOrbit m u w t) ∧
      |stableBoundaryOrbit m u w t 0 - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) ∧
      |stableBoundaryOrbit m u w t 1| ≤ |u| ∧ |stableBoundaryOrbit m u w t 3| ≤ |w| := by
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_global_region hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  have H' := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  change ∀ t ≥ 0, _ ∧ stableBoundaryRegion c (stableBoundaryOrbit m u w t) ∧
    |stableBoundaryOrbit m u w t 0 - stableBoundaryOrbit m u w 0 0| ≤
      8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) ∧
    |stableBoundaryOrbit m u w t 1| ≤ |stableBoundaryOrbit m u w 0 1| ∧
    |stableBoundaryOrbit m u w t 3| ≤ |stableBoundaryOrbit m u w 0 3| at H'
  simpa [hi, stableBoundaryEntry] using H'

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_exists {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    Tendsto (fun t => stableBoundaryOrbit m u w t 0) atTop (𝓝 (stableBoundaryProjection m u w)) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 1) atTop (𝓝 0) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 3) atTop (𝓝 0) ∧
    (∀ t ≥ 0, |stableBoundaryProjection m u w - stableBoundaryOrbit m u w t 0| ≤
      8 * (|stableBoundaryOrbit m u w t 1| + |stableBoundaryOrbit m u w t 3|) ^ 2 / (c + 1)) ∧
    |stableBoundaryProjection m u w - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate x 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_limit hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  obtain ⟨P, hP, hU, hW, htail⟩ := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  have heq : stableBoundaryProjection m u w = P := hP.limUnder_eq
  rw [heq]
  refine ⟨hP, hU, hW, htail, ?_⟩
  have H0 := htail 0 le_rfl
  change |P - stableBoundaryOrbit m u w 0 0| ≤
    8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) at H0
  simpa [hi, stableBoundaryEntry] using H0

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_entranceClockRate (n : WithTop ℕ∞) : ContDiff ℝ n entranceClockRate := by
  unfold entranceClockRate connectionSpeed coupling
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_entranceLogField (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : entranceClockRate y ≠ 0) : ContDiffAt ℝ n entranceLogField y :=
  ((contDiff_entranceClockRate n).contDiffAt.inv hD).smul
    (contDiff_projectiveField n).contDiffAt

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceLogField_active {y : ProjectiveState} (hD : entranceClockRate y ≠ 0) :
    entranceLogField y 2 = y 2 := by
  change (entranceClockRate y)⁻¹ * (entranceClockRate y * y 2) = y 2
  rw [← mul_assoc, inv_mul_cancel₀ hD, one_mul]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_entranceLogClock (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : y 2 ≠ 0) : ContDiffAt ℝ n entranceLogClock y :=
  (contDiff_apply ℝ ℝ 2).contDiffAt.log hv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_entranceOriginalClockRate (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) : ContDiffAt ℝ n entranceOriginalClockRate y := by
  unfold entranceOriginalClockRate
  exact (contDiffAt_const.div (contDiff_projectiveStateDenom n).contDiffAt hD).mul
    (contDiff_entranceClockRate n).contDiffAt

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceLogClock_fderiv {y : ProjectiveState} (hv : y 2 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ entranceLogClock y v = v 2 / y 2 := by
  have H := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y).log hv
  rw [show fderiv ℝ entranceLogClock y = _ from H.fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceLogClock_fderiv_field {y : ProjectiveState} (hv : y 2 ≠ 0) :
    fderiv ℝ entranceLogClock y (projectiveOriginalField y) = entranceOriginalClockRate y := by
  rw [entranceLogClock_fderiv hv]
  change (6 / projectiveStateDenom y * activeVelocity (y 0) (y 1) (y 2) (y 3)) / y 2 = _
  dsimp [entranceOriginalClockRate, entranceClockRate, connectionSpeed, activeVelocity]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.projectiveOriginalField_entranceLog {y : ProjectiveState} (hD : entranceClockRate y ≠ 0) :
    projectiveOriginalField y = entranceOriginalClockRate y • entranceLogField y := by
  unfold entranceOriginalClockRate entranceLogField projectiveOriginalField
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hD, mul_one]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_restart {m c u w s t : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    let Y := stableBoundaryOrbit m u w
    stableBoundaryOrbit (Y s 0) (Y s 1) (Y s 3) t = Y (t + s) := by
  intro Y
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hx : stateConstraint x = 1 :=
    fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have hglobal := stableBoundaryOrbit_global hc hm hu hw s hs
  have hK : 0 < c + 1 := by linarith
  have hAs : 0 < 1 + normalizedMaxCurve x 0 s 0 :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2) hglobal.1
  have hxs := normalizedMaxCurve_forward_of_constraint hx hs
  have hent : stableBoundaryEntry (Y s 0) (Y s 1) (Y s 3) = Y s := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact hglobal.2.1.2.2.1.symm
    · rfl
  have hinv : fromProjectiveState (stableBoundaryEntry (Y s 0) (Y s 1) (Y s 3)) =
      normalizedMaxCurve x 0 s := by
    rw [hent]
    exact fromProjectiveState_toProjectiveState (ne_of_gt hAs) hxs.2.1
  change toProjectiveState (normalizedMaxCurve
    (fromProjectiveState (stableBoundaryEntry (Y s 0) (Y s 1) (Y s 3))) 0 t) = Y (t + s)
  rw [hinv]
  have ht' := normalizedMaxDomain_contains_Ici_of_constraint hxs.2.1 0 ht
  have hretime := normalizedMaxCurve_retime (t₀ := s) ht'
  simp only [sub_zero] at hretime
  rw [hretime, normalizedMaxCurve_rebase
    (normalizedMaxDomain_contains_Ici_of_constraint hx 0 hs)
    (normalizedMaxDomain_contains_Ici_of_constraint hx 0 (add_nonneg ht hs))]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_invariant {m c u w s : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hs : 0 ≤ s) :
    let Y := stableBoundaryOrbit m u w
    stableBoundaryProjection (Y s 0) (Y s 1) (Y s 3) = stableBoundaryProjection m u w := by
  intro Y
  have hP := (stableBoundaryProjection_exists hc hm hu hw).1
  have hshift : Tendsto (fun t => Y (t + s) 0) atTop (𝓝 (stableBoundaryProjection m u w)) :=
    hP.comp (tendsto_atTop_add_const_right atTop s tendsto_id)
  have hnew : Tendsto (fun t => stableBoundaryOrbit (Y s 0) (Y s 1) (Y s 3) t 0)
      atTop (𝓝 (stableBoundaryProjection m u w)) := by
    apply hshift.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [stableBoundaryOrbit_restart hc hm hu hw hs ht]
  exact hnew.limUnder_eq

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entranceClockProjection_active {y v : ProjectiveState} {ζ : ℝ}
    (hD : entranceClockRate y ≠ 0) (hv : y 2 ≠ 0) :
    entranceClockProjection y v ζ 2 = ζ * y 2 := by
  change v 2 - (v 2 / y 2 - ζ) * entranceLogField y 2 = _
  rw [entranceLogField_active hD]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_entranceClockProjection {β v : ℝ → ProjectiveState} {t ζ : ℝ}
    (hβ : HasDerivAt β (projectiveOriginalField (β t)) t)
    (hv : HasDerivAt v (fderiv ℝ projectiveOriginalField (β t) (v t)) t)
    (hw : β t 2 ≠ 0) (hden : projectiveStateDenom (β t) ≠ 0)
    (hD : entranceClockRate (β t) ≠ 0) :
    HasDerivAt (fun s => entranceClockProjection (β s) (v s) ζ)
      (entranceOriginalClockRate (β t) • fderiv ℝ entranceLogField (β t)
        (entranceClockProjection (β t) (v t) ζ)) t := by
  have hF := (contDiffAt_entranceLogField 1 hD).differentiableAt (by norm_num)
  have hwnear : ∀ᶠ y : ProjectiveState in 𝓝 (β t), y 2 ≠ 0 :=
    (continuous_apply 2).continuousAt.eventually_ne hw
  have hDnear : ∀ᶠ y : ProjectiveState in 𝓝 (β t), entranceClockRate y ≠ 0 :=
    continuous_entranceClockRate.continuousAt.eventually_ne hD
  have hclock : (fun y => fderiv ℝ entranceLogClock y (projectiveOriginalField y))
      =ᶠ[𝓝 (β t)] entranceOriginalClockRate := by
    filter_upwards [hwnear] with y hy
    exact entranceLogClock_fderiv_field hy
  have hstate : (fun y => fderiv ℝ (id : ProjectiveState → ProjectiveState) y (projectiveOriginalField y))
      =ᶠ[𝓝 (β t)] (fun y => entranceOriginalClockRate y • entranceLogField y) := by
    filter_upwards [hDnear] with y hy
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using projectiveOriginalField_entranceLog hy
  have hfield : DifferentiableAt ℝ (fun q : ℝ × ProjectiveState => entranceLogField q.2)
      (entranceLogClock (β t), β t) := by fun_prop
  have H := hasDerivAt_coordinate_clock_variation (p := id)
    (field := fun q : ℝ × ProjectiveState => entranceLogField q.2)
    contDiffAt_id (contDiffAt_entranceLogClock 2 hw)
    ((contDiffAt_projectiveOriginalField 1 hden).differentiableAt (by norm_num))
    ((contDiffAt_entranceOriginalClockRate 1 hden).differentiableAt (by norm_num))
    hfield hβ hv hclock hstate
  simp only [fderiv_id, ContinuousLinearMap.id_apply, id_eq] at H
  have hζ := (hF.hasFDerivAt.comp_hasDerivAt t hβ).const_smul ζ
  have heq : (fun s => entranceClockProjection (β s) (v s) ζ) =ᶠ[𝓝 t]
      (fun s => v s - fderiv ℝ entranceLogClock (β s) (v s) • entranceLogField (β s) +
        ζ • entranceLogField (β s)) := by
    filter_upwards [hβ.continuousAt.eventually hwnear] with s hs
    rw [entranceClockProjection, entranceLogClock_fderiv hs, sub_smul]
    module
  apply ((H.add hζ).congr_of_eventuallyEq heq).congr_deriv
  simp only [projectiveOriginalField_entranceLog hD, entranceClockProjection,
    entranceLogClock_fderiv hw, map_sub, map_smul]
  module

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_entranceProjectedFlowVariation {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hw : projectiveOriginalFlow y t₀ t 2 ≠ 0)
    (hclock : entranceClockRate (projectiveOriginalFlow y t₀ t) ≠ 0) (w : ProjectiveState) :
    HasDerivAt (fun s => entranceProjectedFlowVariation y t₀ s w)
      (entranceOriginalClockRate (projectiveOriginalFlow y t₀ t) •
        fderiv ℝ entranceLogField (projectiveOriginalFlow y t₀ t)
          (entranceProjectedFlowVariation y t₀ t w)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_entranceClockProjection (hasDerivAt_projectiveOriginalFlow_time hD ht hA)
    (hasDerivAt_projectiveFlowDifferential_apply hD ht hA w) hw
    (ne_of_gt (toProjectiveState_denom_pos hA hc)) hclock

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entranceProjectedFlowVariation_active {y : ProjectiveState} {t₀ t : ℝ}
    (hv : projectiveOriginalFlow y t₀ t 2 ≠ 0)
    (hD : entranceClockRate (projectiveOriginalFlow y t₀ t) ≠ 0) (w : ProjectiveState) :
    entranceProjectedFlowVariation y t₀ t w 2 = (w 2 / y 2) * projectiveOriginalFlow y t₀ t 2 :=
  entranceClockProjection_active hD hv

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableBoundaryOrbit_two {y : Fin 3 → ℝ} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    ContDiffAt ℝ 2 (fun z : (Fin 3 → ℝ) × ℝ => stableBoundaryOrbit (z.1 0) (z.1 1) (z.1 2) z.2) (y, t) := by
  have hD := stableBoundaryEntry_denom_pos (y 0) (y 1) (y 2)
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hK : 0 < c + 1 := by linarith
  have hA := lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2)
    (stableBoundaryOrbit_global hc hm hu hw t ht).1
  have hentry : ContDiffAt ℝ 2
      (fun z : (Fin 3 → ℝ) × ℝ => (stableBoundaryEntry (z.1 0) (z.1 1) (z.1 2), z.2)) (y, t) := by
    apply ContDiffAt.prodMk _ contDiffAt_snd
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [stableBoundaryEntry] <;> fun_prop
  have H := (contDiffAt_projectiveOriginalFlow_two hD hdom hA).comp (y, t) hentry
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_apply (y : StableState) : stableInclusion y = ![y 0, y 1, 0, y 2] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRestriction_apply (y : ProjectiveState) : stableRestriction y = ![y 0, y 1, y 3] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_entry (y : StableState) :
    stableInclusion y = stableBoundaryEntry (y 0) (y 1) (y 2) := stableInclusion_apply y

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRestriction_inclusion (y : StableState) : stableRestriction (stableInclusion y) = y := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_restriction {y : ProjectiveState} (hy : y 2 = 0) :
    stableInclusion (stableRestriction y) = y := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact hy.symm
  · rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_pos (y : StableState) : 0 < stableBoundaryDenom y := by
  unfold stableBoundaryDenom
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_eq (y : StableState) :
    projectiveStateDenom (stableInclusion y) = stableBoundaryDenom y := by
  change projectiveDenom (y 0) (y 1) 0 (y 2) = _
  unfold projectiveDenom curvature stableBoundaryDenom
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryField_inclusion (y : StableState) :
    projectiveField (stableInclusion y) = stableInclusion (stableBoundaryField y) := by
  obtain ⟨hM, hU, hV, hW⟩ := stable_boundary_field (y 0) (y 1) (y 2)
  ext i
  fin_cases i
  · exact hM
  · exact hU
  · exact hV
  · exact hW

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_inclusion (y : StableState) :
    projectiveOriginalField (stableInclusion y) = stableInclusion (stableOriginalField y) := by
  rw [projectiveOriginalField, stableBoundaryDenom_eq, stableBoundaryField_inclusion,
    stableOriginalField, map_smul]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_restriction {y : ProjectiveState} (hy : y 2 = 0) :
    stableRestriction (projectiveOriginalField y) = stableOriginalField (stableRestriction y) := by
  rw [← stableInclusion_restriction hy, stableOriginalField_inclusion, stableRestriction_inclusion,
    stableRestriction_inclusion]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableBoundaryField (n : WithTop ℕ∞) : ContDiff ℝ n stableBoundaryField := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [stableBoundaryField, stableStrongRate, stableWeakRate] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableBoundaryDenom (n : WithTop ℕ∞) : ContDiff ℝ n stableBoundaryDenom := by
  unfold stableBoundaryDenom
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableOriginalField (n : WithTop ℕ∞) : ContDiff ℝ n stableOriginalField := by
  apply (contDiff_const.div (contDiff_stableBoundaryDenom n)
    (fun y => ne_of_gt (stableBoundaryDenom_pos y))).smul (contDiff_stableBoundaryField n)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_active_zero (m u w : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    stableBoundaryOrbit m u w t 2 = 0 := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have hzero : wallValue 1 x = 0 := by
    simp [x, wallValue, fromProjectiveState, stableBoundaryEntry]
  have H := (normalizedMaxCurve_wall_sign hx ht 1).1.mpr hzero
  change normalizedMaxCurve x 0 t 3 = 0 at H
  change Real.sqrt 3 * normalizedMaxCurve x 0 t 3 / (1 + normalizedMaxCurve x 0 t 0) = 0
  rw [H, mul_zero, zero_div]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableOriginalFlow_eq (y : StableState) (t : ℝ) :
    stableOriginalFlow y t = stableRestriction (stableBoundaryOrbit (y 0) (y 1) (y 2) t) := by
  simp only [stableOriginalFlow, stableInclusion_entry, projectiveOriginalFlow, stableBoundaryOrbit]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableProjectiveFlow_active_zero (y : StableState) {t : ℝ} (ht : 0 ≤ t) :
    projectiveOriginalFlow (stableInclusion y) 0 t 2 = 0 := by
  simpa only [stableInclusion_entry, projectiveOriginalFlow, stableBoundaryOrbit] using
    stableBoundaryOrbit_active_zero (y 0) (y 1) (y 2) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableProjectiveFlow_rate_pos {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    0 < normalizedProjectiveRate (fromProjectiveState (stableInclusion y)) 0 t := by
  have hK : 0 < c + 1 := by linarith
  rw [stableInclusion_entry]
  exact lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2)
    (stableBoundaryOrbit_global hc hm hu hw t ht).1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableOriginalFlow_initial (y : StableState) : stableOriginalFlow y 0 = y := by
  rw [stableOriginalFlow_eq, stableBoundaryOrbit_initial, ← stableInclusion_entry]
  exact stableRestriction_inclusion y

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableFlowDifferential_initial (y : StableState) :
    stableFlowDifferential y 0 = ContinuousLinearMap.id ℝ StableState := by
  rw [stableFlowDifferential, projectiveFlowDifferential_initial
    (by rw [stableBoundaryDenom_eq]; exact stableBoundaryDenom_pos y), ContinuousLinearMap.id_comp]
  ext v i
  exact congrFun (stableRestriction_inclusion v) i

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableOriginalFlow {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    HasDerivAt (stableOriginalFlow y) (stableOriginalField (stableOriginalFlow y t)) t := by
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hm hu hw ht
  have H := stableRestriction.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_projectiveOriginalFlow_time hD hdom hA)
  rw [stableOriginalField_restriction (stableProjectiveFlow_active_zero y ht)] at H
  exact H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stableOriginalFlow {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    HasFDerivAt (fun z => stableOriginalFlow z t) (stableFlowDifferential y t) y := by
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hm hu hw ht
  have H := stableRestriction.hasFDerivAt.comp y
    ((hasFDerivAt_projectiveOriginalFlow_initial hD hdom hA).comp y stableInclusion.hasFDerivAt)
  exact H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableFlowDifferential_apply {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) (v : StableState) :
    HasDerivAt (fun s => stableFlowDifferential y s v)
      (fderiv ℝ stableOriginalField (stableOriginalFlow y t) (stableFlowDifferential y t v)) t := by
  let alpha := projectiveOriginalFlow (stableInclusion y) 0
  let V := fun s => projectiveFlowDifferential (stableInclusion y) 0 s (stableInclusion v)
  let b := fun z : StableState => projectiveOriginalFlow (stableInclusion z) 0 t
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hm hu hw ht
  have hb := (hasFDerivAt_projectiveOriginalFlow_initial hD hdom hA).comp y stableInclusion.hasFDerivAt
  have halpha := hasDerivAt_projectiveOriginalFlow_time hD hdom hA
  have hV := hasDerivAt_projectiveFlowDifferential_apply hD hdom hA (stableInclusion v)
  have hDout : 0 < projectiveStateDenom (alpha t) := by
    have hcon := (normalizedMaxCurve_constraint hdom).trans (fromProjectiveState_constraint (ne_of_gt hD))
    exact toProjectiveState_denom_pos hA hcon
  have heq : (fun z => fderiv ℝ stableRestriction (b z) (projectiveOriginalField (b z))) =ᶠ[𝓝 y]
      (fun z => stableOriginalField (stableRestriction (b z))) := by
    apply Eventually.of_forall
    intro z
    simp only [stableRestriction.fderiv]
    exact stableOriginalField_restriction (stableProjectiveFlow_active_zero z ht)
  have H := hasDerivAt_coordinate_variation stableRestriction.contDiff.contDiffAt
    ((contDiffAt_projectiveOriginalField 1 hDout.ne').differentiableAt (by norm_num))
    ((contDiff_stableOriginalField 1).differentiable (by norm_num) (stableRestriction (alpha t)))
    halpha hV hb rfl rfl heq
  simpa only [stableRestriction.fderiv, stableFlowDifferential, stableOriginalFlow, alpha,
    ContinuousLinearMap.comp_apply] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableBoundaryField {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableBoundaryField (gamma s))
      ((stableBoundaryJacobian (gamma t)).mulVec v) t := by
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · apply (((hm.mul (hu.pow 2)).sub (((hm.add_const 1).mul hu).mul hw)).add
      (hw.pow 2)).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · apply ((((((hasDerivAt_const t (1 : ℝ)).sub (hm.pow 2)).sub
      (hw.pow 2)).add (hu.pow 2)).div_const 2).mul hu).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · apply ((((hm.add_const 1).add (hu.mul hw)).sub (hu.pow 2)).neg.mul hw).congr_deriv
    simp [stableBoundaryJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableBoundaryDenom {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableBoundaryDenom (gamma s))
      (dotProduct (stableDenomGradient (gamma t)) v) t := by
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  apply (((hm.pow 2).const_add 3).add ((hu.sub hw).pow 2)).congr_deriv
  simp [stableDenomGradient, dotProduct, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableOriginalField {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableOriginalField (gamma s))
      ((stableOriginalJacobian (gamma t)).mulVec v) t := by
  have hd := hasDerivAt_stableBoundaryDenom h
  have hf := hasDerivAt_stableBoundaryField h
  apply (((hasDerivAt_const t (6 : ℝ)).div hd
    (stableBoundaryDenom_pos (gamma t)).ne').smul hf).congr_deriv
  ext i
  simp [stableOriginalJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_fderiv (y v : StableState) :
    fderiv ℝ stableOriginalField y v = (stableOriginalJacobian y).mulVec v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf := ((contDiff_stableOriginalField 1).differentiable (by norm_num) y).hasFDerivAt
  have hzero : y + (0 : ℝ) • v = y := by simp
  have H := (hzero.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hzero] using H.unique (hasDerivAt_stableOriginalField hl)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableFlow_variational_equation {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) (v : StableState) :
    HasDerivAt (fun s => stableFlowDifferential y s v)
      ((stableOriginalJacobian (stableOriginalFlow y t)).mulVec (stableFlowDifferential y t v)) t := by
  simpa only [stableOriginalField_fderiv] using
    hasDerivAt_stableFlowDifferential_apply hc hm hu hw ht v

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableRescaledDifferential_initial (K : ℝ) (y : StableState) :
    stableRescaledDifferential K y 0 = ContinuousLinearMap.id ℝ StableState := by
  simp only [stableRescaledDifferential, mul_zero, stableFlowDifferential_initial]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stableRescaledFlow {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasFDerivAt (fun z => stableRescaledFlow K z s) (stableRescaledDifferential K y s) y :=
  hasFDerivAt_stableOriginalFlow hc hm hu hw (mul_nonneg hK.le hs)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableRescaledFlow_variational_equation {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    HasDerivAt (fun r => stableRescaledDifferential K y r v)
      (K • (stableOriginalJacobian (stableRescaledFlow K y s)).mulVec
        (stableRescaledDifferential K y s v)) s := by
  exact (stableFlow_variational_equation hc hm hu hw (mul_nonneg hK.le hs) v).scomp s
    (by simpa using (hasDerivAt_id s).const_mul K)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableOriginalFlow_two {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    ContDiffAt ℝ 2 (fun z : StableState × ℝ => stableOriginalFlow z.1 z.2) (y, t) := by
  simp_rw [stableOriginalFlow_eq]
  exact stableRestriction.contDiff.contDiffAt.comp (y, t)
    (contDiffAt_stableBoundaryOrbit_two hc hm hu hw ht)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableRescaledFlow_two {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (fun z : StableState × ℝ => stableRescaledFlow K z.1 z.2) (y, s) := by
  have H := contDiffAt_stableOriginalFlow_two hc hm hu hw (mul_nonneg hK.le hs)
  have hmap : ContDiffAt ℝ 2 (fun z : StableState × ℝ => (z.1, K * z.2)) (y, s) :=
    contDiffAt_fst.prodMk (contDiffAt_const.mul contDiffAt_snd)
  have H' := H.comp (y, s) hmap
  exact H'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_rate_denom_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableStrongRate (y 0) (y 1) (y 2)| ≤ stableBoundaryDenom y ∧
      |stableWeakRate (y 0) (y 1) (y 2)| ≤ stableBoundaryDenom y := by
  have hK : 0 < c + 1 := by linarith
  have hr := stable_boundary_rates hc hm hu hw
  have hs := (div_le_iff₀ hK).mp hr.1
  have hw' := (div_le_iff₀ hK).mp hr.2
  have hs0 : stableStrongRate (y 0) (y 1) (y 2) ≤ 0 := by nlinarith
  have hw0 : stableWeakRate (y 0) (y 1) (y 2) ≤ 0 := by nlinarith
  rw [abs_of_nonpos hs0, abs_of_nonpos hw0]
  have huw : |y 1 * y 2| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  obtain ⟨huwl, huwu⟩ := abs_le.mp huw
  unfold stableStrongRate stableWeakRate stableBoundaryDenom
  constructor
  · nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]
  · nlinarith [sq_nonneg (y 0 - 1 / 2), sq_nonneg (y 1), sq_nonneg (y 2)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_field_div_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableBoundaryField y 1 / stableBoundaryDenom y| ≤ |y 1| ∧
      |stableBoundaryField y 2 / stableBoundaryDenom y| ≤ |y 2| := by
  have H := stableBoundary_rate_denom_bounds hc hm hu hw
  have hD := stableBoundaryDenom_pos y
  constructor
  · rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    change |stableStrongRate (y 0) (y 1) (y 2) * y 1| ≤ _
    rw [abs_mul, mul_comm _ (stableBoundaryDenom y)]
    exact mul_le_mul_of_nonneg_right H.1 (abs_nonneg _)
  · rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    change |stableWeakRate (y 0) (y 1) (y 2) * y 2| ≤ _
    rw [abs_mul, mul_comm _ (stableBoundaryDenom y)]
    exact mul_le_mul_of_nonneg_right H.2 (abs_nonneg _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundary_polynomial_rows {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    stableBoundaryJacobian y 1 1 + |stableBoundaryJacobian y 1 2| +
        4 * (|y 1| + |y 2|) ^ 2 ≤ -(c + 1) ^ 2 / 16 ∧
    stableBoundaryJacobian y 2 2 + |stableBoundaryJacobian y 2 1| +
        4 * (|y 1| + |y 2|) ^ 2 ≤ -(c + 1) / 8 := by
  have hK : 0 < c + 1 := by linarith
  have hr := stable_boundary_rates hc hm hu hw
  have hs := (div_le_iff₀ hK).mp hr.1
  have hw' := (div_le_iff₀ hK).mp hr.2
  have hb : (|y 1| + |y 2|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hu2 : y 1 ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by norm_num; exact hu)
  have huw : |y 1 * y 2| ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hw (abs_nonneg _) (by norm_num)
  have hcross : |(2 * y 1 - y 2) * y 2| ≤ 3 / 10000 := by
    rw [abs_mul]
    have H : |2 * y 1 - y 2| ≤ 3 / 100 := by
      have H' := abs_sub (2 * y 1) (y 2)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at H'
      linarith
    nlinarith [mul_le_mul H hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 100)]
  constructor
  · change (1 - y 0 ^ 2 - y 2 ^ 2 + 3 * y 1 ^ 2) / 2 + |-y 1 * y 2| + _ ≤ _
    rw [neg_mul, abs_neg]
    unfold stableStrongRate at hs
    nlinarith [sq_nonneg (c + 1 - 3)]
  · change -(y 0 + 1 + 2 * y 1 * y 2 - y 1 ^ 2) + |(2 * y 1 - y 2) * y 2| + _ ≤ _
    unfold stableWeakRate at hw'
    nlinarith [(abs_le.mp huw).1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalJacobian_factor (y : StableState) (i j : Fin 3) :
    stableOriginalJacobian y i j = 6 / stableBoundaryDenom y *
      (stableBoundaryJacobian y i j - stableBoundaryField y i / stableBoundaryDenom y *
        stableDenomGradient y j) := by
  unfold stableOriginalJacobian
  field_simp [(stableBoundaryDenom_pos y).ne']

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_rational_row {a d f g h D b : ℝ}
    (hD : 0 < D) (hb : 0 ≤ b) (hf : |f / D| ≤ b) (hg : |g| ≤ 2 * b) (hh : |h| ≤ 2 * b) :
    6 / D * (a - f / D * g) + |6 / D * (d - f / D * h)| ≤
      6 / D * (a + |d| + 4 * b ^ 2) := by
  have h1 : |f / D * g| ≤ 2 * b ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hf hg (abs_nonneg _) hb]
  have h2 : |f / D * h| ≤ 2 * b ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hf hh (abs_nonneg _) hb]
  rw [abs_mul, abs_of_pos (by positivity : 0 < 6 / D)]
  have H : a - f / D * g + |d - f / D * h| ≤ a + |d| + 4 * b ^ 2 := by
    have H' := abs_sub d (f / D * h)
    nlinarith [(abs_le.mp h1).1]
  have H' := mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ 6 / D)
  nlinarith only [H']

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalJacobian_stable_rows {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    stableOriginalJacobian y 1 1 + |stableOriginalJacobian y 1 2| ≤
        6 / stableBoundaryDenom y * (-(c + 1) ^ 2 / 16) ∧
    stableOriginalJacobian y 2 2 + |stableOriginalJacobian y 2 1| ≤
        6 / stableBoundaryDenom y * (-(c + 1) / 8) := by
  have hD := stableBoundaryDenom_pos y
  have hf := stableBoundary_field_div_bounds hc hm hu hw
  have hr := stableBoundary_polynomial_rows hc hm hu hw
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hg1 : |stableDenomGradient y 1| ≤ 2 * (|y 1| + |y 2|) := by
    change |2 * (y 1 - y 2)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
  have hg2 : |stableDenomGradient y 2| ≤ 2 * (|y 1| + |y 2|) := by
    change |2 * (y 2 - y 1)| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have H := abs_sub (y 2) (y 1)
    linarith
  simp_rw [stableOriginalJacobian_factor]
  constructor
  · exact (stable_rational_row hD hb (hf.1.trans (by linarith [abs_nonneg (y 2)])) hg1 hg2).trans
      (mul_le_mul_of_nonneg_left hr.1 (by positivity))
  · exact (stable_rational_row hD hb (hf.2.trans (by linarith [abs_nonneg (y 1)])) hg2 hg1).trans
      (mul_le_mul_of_nonneg_left hr.2 (by positivity))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledJacobian_stable_rows {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    (c + 1) * (stableOriginalJacobian y 1 1 + |stableOriginalJacobian y 1 2|) ≤
        -3 * (c + 1) / 16 ∧
    (c + 1) * (stableOriginalJacobian y 2 2 + |stableOriginalJacobian y 2 1|) ≤
        -(3 / 8) := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hDup : stableBoundaryDenom y ≤ 2 * (c + 1) ^ 2 := by
    have H := (stable_boundary_denom hc hm hu hw).2
    change projectiveStateDenom (stableBoundaryEntry (y 0) (y 1) (y 2)) ≤ _ at H
    rwa [← stableInclusion_entry, stableBoundaryDenom_eq] at H
  have H := stableOriginalJacobian_stable_rows hc hm hu hw
  constructor
  · apply (mul_le_mul_of_nonneg_left H.1 hK.le).trans
    have heq : (c + 1) * (6 / stableBoundaryDenom y * (-(c + 1) ^ 2 / 16)) =
        (-3 * (c + 1) ^ 3 / 8) / stableBoundaryDenom y := by ring
    rw [heq]
    apply (div_le_iff₀ hD).mpr
    nlinarith [mul_le_mul_of_nonneg_left hDup hK.le]
  · apply (mul_le_mul_of_nonneg_left H.2 hK.le).trans
    have heq : (c + 1) * (6 / stableBoundaryDenom y * (-(c + 1) / 8)) =
        (-3 * (c + 1) ^ 2 / 4) / stableBoundaryDenom y := by ring
    rw [heq]
    apply (div_le_iff₀ hD).mpr
    linarith

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledFlow_band {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 0 - c| ≤ 1 / 10 ∧
    |stableRescaledFlow (c + 1) y s 1| ≤ 1 / 100 ∧
    |stableRescaledFlow (c + 1) y s 2| ≤ 1 / 100 := by
  have ht : 0 ≤ (c + 1) * s := mul_nonneg (by linarith) hs
  have H := (stableBoundaryOrbit_global hc hm hu hw ((c + 1) * s) ht).2.1
  simp only [stableRescaledFlow, stableOriginalFlow_eq, stableRestriction_apply]
  exact ⟨H.1, H.2.1, H.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_lower {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    (c + 1) ^ 2 ≤ 3 * stableBoundaryDenom y ∧ c + 1 ≤ stableBoundaryDenom y := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  unfold stableBoundaryDenom
  constructor
  · nlinarith [sq_nonneg (y 1 - y 2)]
  · nlinarith [sq_nonneg (y 1 - y 2), sq_nonneg (c + 1 - 3)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_scaled_entry_bound {y : StableState} {c B : ℝ} {i j : Fin 3}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) (hB : 0 ≤ B)
    (hentry : |stableBoundaryJacobian y i j -
      stableBoundaryField y i / stableBoundaryDenom y * stableDenomGradient y j| ≤ 3 * (c + 1) * B) :
    |(c + 1) * stableOriginalJacobian y i j| ≤ 64 * B := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hscale : 6 * (c + 1) ^ 2 / stableBoundaryDenom y ≤ 18 := by
    apply (div_le_iff₀ hD).mpr
    nlinarith [(stableBoundaryDenom_lower hc hm).1]
  rw [stableOriginalJacobian_factor, abs_mul, abs_of_pos hK, abs_mul,
    abs_of_pos (by positivity : 0 < 6 / stableBoundaryDenom y)]
  calc
    _ ≤ (c + 1) * (6 / stableBoundaryDenom y * (3 * (c + 1) * B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hentry (by positivity)) hK.le
    _ = (6 * (c + 1) ^ 2 / stableBoundaryDenom y) * (3 * B) := by ring
    _ ≤ 18 * (3 * B) := mul_le_mul_of_nonneg_right hscale (by positivity)
    _ ≤ 64 * B := by linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledJacobian_center_column {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * stableOriginalJacobian y 1 0| ≤ 64 * |y 1| ∧
    |(c + 1) * stableOriginalJacobian y 2 0| ≤ 64 * |y 2| := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have H := stableBoundary_field_div_bounds hc hm hu hw
  have hg : |stableDenomGradient y 0| ≤ 2 * (c + 1) := by
    change |2 * y 0| ≤ _
    rw [abs_of_nonneg (by positivity)]
    linarith
  constructor
  · apply stable_scaled_entry_bound hc hm (abs_nonneg _)
    have hf : |stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
        2 * (c + 1) * |y 1| := by
      rw [abs_mul]
      nlinarith [mul_le_mul H.1 hg (abs_nonneg _) (abs_nonneg _)]
    have hp : |stableBoundaryJacobian y 1 0| ≤ (c + 1) * |y 1| := by
      change |-y 0 * y 1| ≤ _
      rw [abs_mul, abs_neg, abs_of_nonneg hm0]
      exact mul_le_mul_of_nonneg_right hmK (abs_nonneg _)
    have H' := abs_sub (stableBoundaryJacobian y 1 0)
      (stableBoundaryField y 1 / stableBoundaryDenom y * stableDenomGradient y 0)
    linarith
  · apply stable_scaled_entry_bound hc hm (abs_nonneg _)
    have hf : |stableBoundaryField y 2 / stableBoundaryDenom y * stableDenomGradient y 0| ≤
        2 * (c + 1) * |y 2| := by
      rw [abs_mul]
      nlinarith [mul_le_mul H.2 hg (abs_nonneg _) (abs_nonneg _)]
    have hp : |stableBoundaryJacobian y 2 0| ≤ (c + 1) * |y 2| := by
      change |-y 2| ≤ _
      rw [abs_neg]
      nlinarith [abs_nonneg (y 2)]
    have H' := abs_sub (stableBoundaryJacobian y 2 0)
      (stableBoundaryField y 2 / stableBoundaryDenom y * stableDenomGradient y 0)
    linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledFlow_wall_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 1| ≤ |y 1| * Real.exp (-3 * (c + 1) / 8 * s) ∧
    |stableRescaledFlow (c + 1) y s 2| ≤ |y 2| * Real.exp (-(3 / 4) * s) := by
  let x := fromProjectiveState (stableBoundaryEntry (y 0) (y 1) (y 2))
  let Y := stableBoundaryOrbit (y 0) (y 1) (y 2)
  let z := normalizedStableClock x 0 0 c
  have hK : 0 < c + 1 := by linarith
  have ht : 0 ≤ (c + 1) * s := mul_nonneg hK.le hs
  have hx : stateConstraint x = 1 :=
    fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos (y 0) (y 1) (y 2)))
  have hg := stableBoundaryOrbit_global hc hm hu hw
  have hdec := (normalized_stable_prefix_estimates hx hc (le_refl 0) ht
    (fun r hr => lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2) (hg r hr.1).1)
    (fun r hr => (hg r hr.1).2.1)).2.1 ((c + 1) * s) ⟨ht, le_rfl⟩
  have hz : 3 * s ≤ z ((c + 1) * s) := by
    have H := normalizedStableClock_lower hx hc (le_refl 0) ht (fun r hr => (hg r hr.1).1)
    convert! H using 1
    simp only [sub_zero]
    field_simp
  have hU : |Y ((c + 1) * s) 1| ≤ |y 1| * Real.exp (-(c + 1) / 8 * z ((c + 1) * s)) := by
    have H := hdec.1
    change |Y ((c + 1) * s) 1| ≤ |Y 0 1| * Real.exp (-(c + 1) / 8 * z ((c + 1) * s)) at H
    simpa [Y, stableBoundaryOrbit_initial, stableBoundaryEntry] using H
  have hW : |Y ((c + 1) * s) 3| ≤ |y 2| * Real.exp (-(1 / 4) * z ((c + 1) * s)) := by
    have H := hdec.2
    change |Y ((c + 1) * s) 3| ≤ |Y 0 3| * Real.exp (-(1 / 4) * z ((c + 1) * s)) at H
    simpa [Y, stableBoundaryOrbit_initial, stableBoundaryEntry] using H
  simp only [stableRescaledFlow, stableOriginalFlow_eq, stableRestriction_apply]
  constructor
  · exact hU.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_left hz hK.le])) (abs_nonneg _))
  · exact hW.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (abs_nonneg _))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRescaledFlow_amplitude_decay {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 1| + |stableRescaledFlow (c + 1) y s 2| ≤
      (|y 1| + |y 2|) * Real.exp (-s / 2) := by
  have H := stableRescaledFlow_wall_decay hc hm hu hw hs
  have hU : Real.exp (-3 * (c + 1) / 8 * s) ≤ Real.exp (-s / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hW : Real.exp (-(3 / 4) * s) ≤ Real.exp (-s / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have H' := add_le_add (H.1.trans (mul_le_mul_of_nonneg_left hU (abs_nonneg _)))
    (H.2.trans (mul_le_mul_of_nonneg_left hW (abs_nonneg _)))
  nlinarith only [H']

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledJacobian_signedRowSum {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (i : Fin 3) :
    signedRowSum ((c + 1) • stableOriginalJacobian y) i ≤ 256 * (|y 1| + |y 2|) := by
  have hK : 0 < c + 1 := by linarith
  have hb : 0 ≤ |y 1| + |y 2| := by positivity
  have hb1 : |y 1| + |y 2| ≤ 1 := by linarith
  have hb2 : (|y 1| + |y 2|) ^ 2 ≤ |y 1| + |y 2| := by nlinarith
  have H := stableRescaledJacobian_center_bounds hc hm hu hw
  have C := stableRescaledJacobian_center_column hc hm hu hw
  have S := stableRescaledJacobian_stable_rows hc hm hu hw
  simp only [abs_mul, abs_of_pos hK] at H C
  have hfin : Finset.univ = ({0, 1, 2} : Finset (Fin 3)) := by decide
  fin_cases i
  · simp [signedRowSum, hfin, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hK]
    have hd := mul_le_mul_of_nonneg_left (le_abs_self (stableOriginalJacobian y 0 0)) hK.le
    nlinarith only [H.1, H.2.1, H.2.2, hd, hb2, hb]
  · simp [signedRowSum, hfin, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hK]
    nlinarith only [S.1, C.1, hc, abs_nonneg (y 1), abs_nonneg (y 2)]
  · simp [signedRowSum, hfin, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hK]
    nlinarith only [S.2, C.2, abs_nonneg (y 1), abs_nonneg (y 2)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledDifferential_bound {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    ‖stableRescaledDifferential (c + 1) y s v‖ ≤
      Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖ := by
  let b := |y 1| + |y 2|
  let J := fun r => stableRescaledDifferential (c + 1) y r v
  let A := fun r => (c + 1) • stableOriginalJacobian (stableRescaledFlow (c + 1) y r)
  let z := fun r => 512 * b * (1 - Real.exp (-r / 2))
  have hK : 0 < c + 1 := by linarith
  have hJ (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt J ((A r).mulVec (J r)) r := by
    simpa only [A, Matrix.smul_mulVec] using
      stableRescaledFlow_variational_equation hK hc hm hu hw hr.1 v
  have hz (r : ℝ) : HasDerivAt z (256 * b * Real.exp (-r / 2)) r := by
    convert! ((hasDerivAt_const r (1 : ℝ)).sub (((hasDerivAt_id r).neg.div_const 2).exp)).const_mul
      (512 * b) using 1
    dsimp
    ring
  have hrow (r : ℝ) (hr : r ∈ Ico 0 s) (i : Fin 3) :
      signedRowSum (A r) i ≤ 256 * b * Real.exp (-r / 2) := by
    obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hr.1
    have H := stableRescaledJacobian_signedRowSum hc hm' hu' hw' i
    have H' := mul_le_mul_of_nonneg_left (stableRescaledFlow_amplitude_decay hc hm hu hw hr.1)
      (by norm_num : (0 : ℝ) ≤ 256)
    exact H.trans (by nlinarith only [H'])
  have H := norm_le_exp_of_signedRowSum (HasDerivAt.continuousOn hJ)
    (fun r hr => hJ r (Ico_subset_Icc_self hr))
    (HasDerivAt.continuousOn (fun r _ => hz r)) (fun r _ => hz r) hrow s ⟨hs, le_rfl⟩
  have hzero : J 0 = v := by simp only [J, stableRescaledDifferential_initial, ContinuousLinearMap.id_apply]
  have hz0 : z 0 = 0 := by simp [z]
  rw [hzero, hz0, sub_zero] at H
  have hzb : z s ≤ 512 * b := by
    have hb : 0 ≤ b := by dsimp [b]; positivity
    dsimp [z]
    nlinarith [Real.exp_pos (-s / 2)]
  have H' := H.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzb) (norm_nonneg v))
  simpa only [mul_comm] using H'

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.stableVariationCenterBudget_nonneg (y v : StableState) : 0 ≤ stableVariationCenterBudget y v := by
  unfold stableVariationCenterBudget
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.stableRescaledJacobian_center_apply {y v : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |(c + 1) * (stableOriginalJacobian y).mulVec v 0| ≤
      64 * (|y 1| + |y 2|) ^ 2 * |v 0| + 128 * (|y 1| + |y 2|) * ‖![v 1, v 2]‖ := by
  have H := stableRescaledJacobian_center_bounds hc hm hu hw
  have hv1 : |v 1| ≤ ‖![v 1, v 2]‖ := by
    simpa only [Real.norm_eq_abs, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 0
  have hv2 : |v 2| ≤ ‖![v 1, v 2]‖ := by
    simpa only [Real.norm_eq_abs, Matrix.cons_val_one, Matrix.cons_val_zero] using norm_le_pi_norm ![v 1, v 2] 1
  have heq : (c + 1) * (stableOriginalJacobian y).mulVec v 0 =
      ((c + 1) * stableOriginalJacobian y 0 0) * v 0 +
      (((c + 1) * stableOriginalJacobian y 0 1) * v 1 +
       ((c + 1) * stableOriginalJacobian y 0 2) * v 2) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  rw [heq]
  have htri := (abs_add_le (((c + 1) * stableOriginalJacobian y 0 0) * v 0)
    ((((c + 1) * stableOriginalJacobian y 0 1) * v 1) +
      (((c + 1) * stableOriginalJacobian y 0 2) * v 2))).trans
        (add_le_add (le_refl _) (abs_add_le _ _))
  simp only [abs_mul] at htri
  have h0 := mul_le_mul_of_nonneg_right H.1 (abs_nonneg (v 0))
  have h1 := mul_le_mul H.2.1 hv1 (abs_nonneg _) (by positivity)
  have h2 := mul_le_mul H.2.2 hv2 (abs_nonneg _) (by positivity)
  simp only [abs_mul] at h0 h1 h2
  nlinarith only [htri, h0, h1, h2]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.stableRescaledDifferential_center_rate {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    |(c + 1) * (stableOriginalJacobian (stableRescaledFlow (c + 1) y s)).mulVec
      (stableRescaledDifferential (c + 1) y s v) 0| ≤
      stableVariationCenterBudget y v * Real.exp (-s / 2) := by
  let b := |y 1| + |y 2|
  let Y := stableRescaledFlow (c + 1) y s
  let J := stableRescaledDifferential (c + 1) y s v
  let B := |Y 1| + |Y 2|
  let M := Real.exp (512 * b) * ‖v‖
  let N := ‖![v 1, v 2]‖
  let e := Real.exp (-s / 2)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hN : 0 ≤ N := norm_nonneg _
  have he : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨hm', hu', hw'⟩ := stableRescaledFlow_band hc hm hu hw hs
  have H := stableRescaledJacobian_center_apply (v := J) hc hm' hu' hw'
  have hBe : B ≤ b * e := stableRescaledFlow_amplitude_decay hc hm hu hw hs
  have hBb : B ≤ b := hBe.trans (mul_le_of_le_one_right hb he1)
  have hB2 : B ^ 2 ≤ b ^ 2 * e := by
    nlinarith only [mul_le_mul hBb hBe hB hb]
  have hJ0 : |J 0| ≤ M := by
    have H' : |J 0| ≤ ‖J‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm J 0
    exact H'.trans (stableRescaledDifferential_bound hc hm hu hw hs v)
  have hZ : ‖![J 1, J 2]‖ ≤ N + 256 * b * M := by
    have H' : ‖![J 1, J 2]‖ ≤ (N + 256 * b * M) * Real.exp (-s / 4) := by
      convert! stableRescaledDifferential_stable_decay hc hm hu hw hs v using 1
      dsimp [M, b, N]
      ring
    exact H'.trans (mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by linarith)))
  have h1 := mul_le_mul hB2 hJ0 (abs_nonneg _) (by positivity : 0 ≤ b ^ 2 * e)
  have h2 := mul_le_mul hBe hZ (norm_nonneg _) (mul_nonneg hb he)
  change |(c + 1) * (stableOriginalJacobian Y).mulVec J 0| ≤ 64 * B ^ 2 * |J 0| +
    128 * B * ‖![J 1, J 2]‖ at H
  have hout : |(c + 1) * (stableOriginalJacobian Y).mulVec J 0| ≤
      (128 * b * N + 33000 * b ^ 2 * M) * e := by
    nlinarith only [H, h1, h2, mul_nonneg (mul_nonneg (sq_nonneg b) hM) he]
  convert! hout using 1
  dsimp [stableVariationCenterBudget, b, N, M, e]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.stableRescaledDifferential_center_tail {y : StableState} {c a t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ha : 0 ≤ a) (hat : a ≤ t) (v : StableState) :
    |stableRescaledDifferential (c + 1) y t v 0 - stableRescaledDifferential (c + 1) y a v 0| ≤
      2 * stableVariationCenterBudget y v * Real.exp (-a / 2) := by
  let C := stableVariationCenterBudget y v
  have hC : 0 ≤ C := stableVariationCenterBudget_nonneg y v
  have hK : 0 < c + 1 := by linarith
  have hf (r : ℝ) (hr : r ∈ Icc a t) :=
    hasDerivAt_pi.mp (stableRescaledFlow_variational_equation hK hc hm hu hw (ha.trans hr.1) v) 0
  have hcont : Continuous (fun r : ℝ => C * Real.exp (-r / 2)) := by fun_prop
  have H := abs_sub_le_integral_bound hat hf hcont.continuousOn
    (fun r hr => stableRescaledDifferential_center_rate hc hm hu hw (ha.trans hr.1) v)
  have HI := integral_le_of_exp_decay (f := fun r : ℝ => C * Real.exp (-r / 2))
    (B := C * Real.exp (-a / 2)) (c := (1 / 2 : ℝ)) hat (by norm_num)
    (by positivity) hcont.continuousOn (fun r _ => ?_)
  · exact H.trans (by convert! HI using 1; ring)
  · have heq : C * Real.exp (-r / 2) =
        (C * Real.exp (-a / 2)) * Real.exp (-(1 / 2) * (r - a)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring
    exact heq.le

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.stableRescaledDifferential_center_drift {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    |stableRescaledDifferential (c + 1) y s v 0 - v 0| ≤ 2 * stableVariationCenterBudget y v := by
  simpa only [stableRescaledDifferential_initial, ContinuousLinearMap.id_apply, neg_zero, zero_div,
    Real.exp_zero, mul_one] using stableRescaledDifferential_center_tail hc hm hu hw (le_refl 0) hs v

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableCenterTailCoefficient_nonneg (y : StableState) : 0 ≤ stableCenterTailCoefficient y := by
  unfold stableCenterTailCoefficient
  positivity

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableVariationCenterBudget_le_norm (y v : StableState) :
    stableVariationCenterBudget y v ≤ stableCenterTailCoefficient y * ‖v‖ := by
  have hv : ‖![v 1, v 2]‖ ≤ ‖v‖ := by
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 1
    · exact norm_le_pi_norm v 2
  have H := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 128 * (|y 1| + |y 2|))
  unfold stableVariationCenterBudget stableCenterTailCoefficient
  nlinarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableCenterDifferential_tail {y : StableState} {c a t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ha : 0 ≤ a) (hat : a ≤ t) :
    ‖stableCenterDifferential c y t - stableCenterDifferential c y a‖ ≤
      2 * stableCenterTailCoefficient y * Real.exp (-a / 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [stableCenterTailCoefficient_nonneg y])
  intro v
  change |stableRescaledDifferential (c + 1) y t v 0 - stableRescaledDifferential (c + 1) y a v 0| ≤ _
  have H := stableRescaledDifferential_center_tail hc hm hu hw ha hat v
  have H' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (stableVariationCenterBudget_le_norm y v) (by norm_num : (0 : ℝ) ≤ 2))
    (Real.exp_pos (-a / 2)).le
  exact H.trans (by nlinarith only [H'])

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableCenterTailCoefficient_decay (y : StableState) :
    Tendsto (fun t : ℝ => 2 * stableCenterTailCoefficient y * Real.exp (-t / 2)) atTop (𝓝 0) := by
  have H := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) tendsto_id)).const_mul
      (2 * stableCenterTailCoefficient y)
  convert! H using 1
  · ext t
    simp only [Function.comp_def, id_eq]
    congr 2
    ring
  · simp

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableCenterDifferential_tendsto {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    Tendsto (stableCenterDifferential c y) atTop (𝓝 (stableCenterDifferentialLimit c y)) := by
  have hC : CauchySeq (stableCenterDifferential c y) := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.mp ((stableCenterTailCoefficient_decay y).eventually (gt_mem_nhds hε))
    refine ⟨max R 0, fun t ht => ?_⟩
    rw [dist_eq_norm]
    exact (stableCenterDifferential_tail hc hm hu hw (le_max_right _ _) ht).trans_lt
      (hR _ (le_max_left _ _))
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.mp hC
  have heq : stableCenterDifferentialLimit c y = L := hL.limUnder_eq
  rwa [heq]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableCenterDifferentialLimit_tail {y : StableState} {c a : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ha : 0 ≤ a) :
    ‖stableCenterDifferentialLimit c y - stableCenterDifferential c y a‖ ≤
      2 * stableCenterTailCoefficient y * Real.exp (-a / 2) := by
  apply le_of_tendsto (((stableCenterDifferential_tendsto hc hm hu hw).sub_const
    (stableCenterDifferential c y a)).norm)
  filter_upwards [eventually_ge_atTop a] with t ht
  exact stableCenterDifferential_tail hc hm hu hw ha ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isOpen_stableParameterDomain (c : ℝ) : IsOpen (stableParameterDomain c) :=
  (isOpen_lt ((continuous_apply 0).sub continuous_const).abs continuous_const).inter
    ((isOpen_lt (continuous_apply 1).abs continuous_const).inter
      (isOpen_lt (continuous_apply 2).abs continuous_const))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stableCenterApproximation {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasFDerivAt (stableCenterApproximation c s) (stableCenterDifferential c y s) y :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt.comp y
    (hasFDerivAt_stableRescaledFlow (by linarith : 0 < c + 1) hc hm hu hw hs)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableCenterApproximation_two {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (stableCenterApproximation c s) y := by
  have H := contDiffAt_stableRescaledFlow_two (by linarith : 0 < c + 1) hc hm hu hw hs
  have hmap : ContDiffAt ℝ 2 (fun z : StableState => (z, s)) y := contDiffAt_id.prodMk contDiffAt_const
  have H' := H.comp y hmap
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff.contDiffAt.comp y H'

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.continuousOn_stableCenterDifferential {c s : ℝ} (hc : 2 ≤ c) (hs : 0 ≤ s) :
    ContinuousOn (fun y => stableCenterDifferential c y s) (stableParameterDomain c) := by
  intro y hy
  have H := ((contDiffAt_stableCenterApproximation_two hc hy.1.le hy.2.1.le hy.2.2.le hs).fderiv_right
    (m := 1) (by norm_num)).continuousAt
  have heq : (fun z => stableCenterDifferential c z s) =ᶠ[𝓝 y] fderiv ℝ (stableCenterApproximation c s) := by
    filter_upwards [(isOpen_stableParameterDomain c).mem_nhds hy] with z hz
    exact (hasFDerivAt_stableCenterApproximation hc hz.1.le hz.2.1.le hz.2.2.le hs).fderiv.symm
  exact (H.congr_of_eventuallyEq heq).continuousWithinAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableCenterTailCoefficient_uniform {y : StableState}
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    stableCenterTailCoefficient y ≤ 2 + 4 * Real.exp 6 := by
  have hb : |y 1| + |y 2| ≤ 1 / 100 := by linarith
  have hb2 : (|y 1| + |y 2|) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).mpr hb
  have he : Real.exp (512 * (|y 1| + |y 2|)) ≤ Real.exp 6 :=
    Real.exp_le_exp.mpr (by linarith)
  have H := mul_le_mul hb2 he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ (1 / 100) ^ 2)
  unfold stableCenterTailCoefficient
  nlinarith [Real.exp_pos 6]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableCenterDifferential_uniform {c : ℝ} (hc : 2 ≤ c) :
    TendstoUniformlyOn (fun n : ℕ => fun y => stableCenterDifferential c y n)
      (stableCenterDifferentialLimit c) atTop (stableParameterDomain c) := by
  have hdec : Tendsto (fun n : ℕ => 2 * (2 + 4 * Real.exp 6) * Real.exp (-(n : ℝ) / 2)) atTop (𝓝 0) := by
    have H := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) tendsto_natCast_atTop_atTop)).const_mul
        (2 * (2 + 4 * Real.exp 6))
    convert! H using 1
    · ext n
      simp only [Function.comp_def]
      congr 2
      ring
    · simp
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hdec.eventually (gt_mem_nhds hε)] with n hn
  intro y hy
  rw [dist_eq_norm]
  have H := stableCenterDifferentialLimit_tail hc hy.1.le hy.2.1.le hy.2.2.le (Nat.cast_nonneg n)
  have H' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (stableCenterTailCoefficient_uniform hy.2.1.le hy.2.2.le)
      (by norm_num : (0 : ℝ) ≤ 2)) (Real.exp_pos (-(n : ℝ) / 2)).le
  exact H.trans_lt (H'.trans_lt hn)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.continuousOn_stableCenterDifferentialLimit {c : ℝ} (hc : 2 ≤ c) :
    ContinuousOn (stableCenterDifferentialLimit c) (stableParameterDomain c) :=
  (stableCenterDifferential_uniform hc).continuousOn
    (Eventually.of_forall (fun n : ℕ => continuousOn_stableCenterDifferential hc (Nat.cast_nonneg n))).frequently

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableBoundaryProjection_one {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 1 (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y := by
  apply contDiffAt_one_iff.mpr
  refine ⟨stableCenterDifferentialLimit (y 0), stableParameterDomain (y 0),
    (isOpen_stableParameterDomain (y 0)).mem_nhds ⟨by simp, hu, hw⟩,
    continuousOn_stableCenterDifferentialLimit hm, ?_⟩
  intro z hz
  exact hasFDerivAt_stableBoundaryProjection_in_band hm hz.1 hz.2.1 hz.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_fderiv_eq {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y =
      stableCenterDifferentialLimit c y :=
  (hasFDerivAt_stableBoundaryProjection_in_band hc hm hu hw).fderiv

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_fderiv_drift {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (v : StableState) :
    |fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y v - v 0| ≤
      2 * stableVariationCenterBudget y v := by
  rw [stableBoundaryProjection_fderiv_eq hc hm hu hw]
  have heval : ContinuousAt (fun L : StableState →L[ℝ] ℝ => L v) (stableCenterDifferentialLimit c y) :=
    continuousAt_id.clm_apply continuousAt_const
  have H := heval.tendsto.comp (stableCenterDifferential_tendsto hc hm.le hu.le hw.le)
  apply le_of_tendsto ((H.sub_const (v 0)).abs)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact stableRescaledDifferential_center_drift hc hm.le hu.le hw.le hs v

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_annihilates_field {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y
      (stableBoundaryField y) = 0 := by
  let p := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  have hd : HasFDerivAt p (fderiv ℝ p y) y :=
    ((contDiffAt_stableBoundaryProjection_one hm hu hw).differentiableAt (by norm_num)).hasFDerivAt
  have hflow : HasDerivAt (stableOriginalFlow y) (stableOriginalField y) 0 := by
    simpa only [stableOriginalFlow_initial] using hasDerivAt_stableOriginalFlow hm
      (by simp : |y 0 - y 0| ≤ (1 : ℝ) / 40) hu.le hw.le (le_refl 0)
  have hd' : HasFDerivAt p (fderiv ℝ p y) (stableOriginalFlow y 0) := by
    rw [stableOriginalFlow_initial]
    exact hd
  have H := hd'.comp_hasDerivAt 0 hflow
  have heq (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : p (stableOriginalFlow y t) = p y := by
    simp only [p, stableOriginalFlow_eq, stableRestriction_apply]
    exact stableBoundaryProjection_invariant hm (by simp : |y 0 - y 0| ≤ (1 : ℝ) / 40) hu.le hw.le ht
  have hconst : HasDerivWithinAt (fun t => p (stableOriginalFlow y t)) 0 (Ici 0) 0 :=
    (hasDerivWithinAt_const 0 (Ici 0) (p y)).congr_of_mem heq (by simp)
  have hzero : fderiv ℝ p y (stableOriginalField y) = 0 :=
    (H.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
      (hconst.derivWithin (uniqueDiffWithinAt_Ici 0))
  rw [stableOriginalField, map_smul, smul_eq_mul] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left
    (div_ne_zero (by norm_num) (stableBoundaryDenom_pos y).ne')

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableBoundaryProjection_two {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 2 (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y :=
  contDiffAt_stableBoundaryProjection_two_in_band hm (by simp) hu hw

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_entranceStablePhase_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 2 entranceStablePhase y :=
  (contDiffAt_stableBoundaryProjection_two (y := stableRestriction y) hm hu hw).comp y
    stableRestriction.contDiff.contDiffAt

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStablePhase_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceStablePhase y v =
      fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
        (stableRestriction y) (stableRestriction v) := by
  have H := ((contDiffAt_stableBoundaryProjection_two (y := stableRestriction y) hm hu hw).differentiableAt
    (by norm_num)).hasFDerivAt.comp y stableRestriction.hasFDerivAt
  exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) H.fderiv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStablePartial_active {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    entranceStablePartial y 2 = 0 := by
  rw [entranceStablePartial, entranceStablePhase_fderiv hm hu hw]
  have hz : stableRestriction (Pi.single (2 : Fin 4) (1 : ℝ)) = 0 := by
    ext i
    fin_cases i <;> simp [stableRestriction]
  rw [hz, map_zero]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.linearForm_four_coordinates (L : ProjectiveState →L[ℝ] ℝ) (v : ProjectiveState) :
    L v = L (Pi.single 0 1) * v 0 + L (Pi.single 1 1) * v 1 +
      L (Pi.single 2 1) * v 2 + L (Pi.single 3 1) * v 3 := by
  have heq : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 +
      v 2 • Pi.single 2 1 + v 3 • Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [heq]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStablePhase_fderiv_coordinates {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceStablePhase y v = entranceStablePartial y 0 * v 0 +
      entranceStablePartial y 1 * v 1 + entranceStablePartial y 3 * v 3 := by
  have H := linearForm_four_coordinates (fderiv ℝ entranceStablePhase y) v
  change _ = entranceStablePartial y 0 * v 0 + entranceStablePartial y 1 * v 1 +
    entranceStablePartial y 2 * v 2 + entranceStablePartial y 3 * v 3 at H
  simpa only [entranceStablePartial_active hm hu hw, zero_mul, add_zero] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStablePhase_fderiv_field {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    fderiv ℝ entranceStablePhase y (projectiveField y) =
      y 1 * y 2 * ((1 - y 0) * entranceStablePartial y 0 +
        y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3)) -
      y 2 ^ 2 * (entranceStablePartial y 0 + y 1 / 2 * entranceStablePartial y 1) := by
  have hzero : fderiv ℝ entranceStablePhase y
      (stableInclusion (stableBoundaryField (stableRestriction y))) = 0 := by
    rw [entranceStablePhase_fderiv hm hu hw, stableRestriction_inclusion]
    exact stableBoundaryProjection_annihilates_field (y := stableRestriction y) hm hu hw
  rw [entranceStablePhase_fderiv_coordinates hm hu hw] at hzero ⊢
  simp [stableInclusion_apply, stableRestriction_apply, stableBoundaryField] at hzero
  dsimp [projectiveField, phaseVelocity, strongVelocity, weakVelocity, coupling,
    stableStrongRate, stableWeakRate] at hzero ⊢
  linear_combination hzero

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStableRadius_pos {y : ProjectiveState} (hv : 0 < y 2) :
    0 < entranceStableRadius y := coreRadius_pos hv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStableRadius_sq (y : ProjectiveState) :
    entranceStableRadius y ^ 2 = (entranceStablePhase y - 1) ^ 2 + y 2 ^ 2 :=
  coreRadius_sq _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_entranceStableRadius_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    ContDiffAt ℝ 2 entranceStableRadius y := by
  have hP := contDiffAt_entranceStablePhase_two hm hu hw
  have hV : ContDiffAt ℝ 2 (fun z : ProjectiveState => z 2) y := by fun_prop
  exact (((hP.sub contDiffAt_const).pow 2).add (hV.pow 2)).sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStableRadius_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2)
    (v : ProjectiveState) :
    fderiv ℝ entranceStableRadius y v =
      ((entranceStablePhase y - 1) * fderiv ℝ entranceStablePhase y v + y 2 * v 2) /
        entranceStableRadius y := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).differentiableAt (by norm_num)
  have H := (((hP.hasFDerivAt.sub_const 1).pow 2).add
    ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y).pow 2)).sqrt
      (by change (entranceStablePhase y - 1) ^ 2 + y 2 ^ 2 ≠ 0; positivity)
  change HasFDerivAt entranceStableRadius _ y at H
  rw [H.fderiv]
  simp only [Pi.add_apply, smul_apply, add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  change _ = _ / Real.sqrt ((entranceStablePhase y - 1) ^ 2 + y 2 ^ 2)
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStableRadius_log_rate {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    fderiv ℝ entranceStableRadius y (projectiveField y) / entranceClockRate y =
      y 1 * y 2 * entranceRadialStrongCoefficient y + y 2 ^ 2 * entranceRadialWeakCoefficient y := by
  rw [entranceStableRadius_fderiv hm hu hw hv, entranceStablePhase_fderiv_field hm hu hw]
  change ((_ - 1) * _ + y 2 * activeVelocity (y 0) (y 1) (y 2) (y 3)) / _ / _ = _
  unfold entranceRadialStrongCoefficient entranceRadialWeakCoefficient entranceWeakNumerator
    entranceClockRate connectionSpeed activeVelocity coupling
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStablePhase_small_wall_bounds {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 10000) (hw : |y 3| ≤ 1 / 10000) :
    |entranceStablePhase y - y 0| ≤ 1 / 100 ∧
      |entranceStablePartial y 0 - 1| ≤ 1 / 2 := by
  have hu' : |y 1| < 1 / 200 := by linarith
  have hw' : |y 3| < 1 / 200 := by linarith
  let b := |y 1| + |y 3|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 / 5000 := by dsimp [b]; linarith
  have hb2 : b ^ 2 ≤ (1 / 5000 : ℝ) ^ 2 := pow_le_pow_left₀ hb hb1 2
  have hval : |entranceStablePhase y - y 0| ≤ 8 * b ^ 2 / (y 0 + 1) :=
    (stableBoundaryProjection_exists hm (by simp) hu'.le hw'.le).2.2.2.2
  have hvec : stableRestriction (Pi.single (0 : Fin 4) (1 : ℝ)) = Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [stableRestriction]
  have hd := stableBoundaryProjection_fderiv_drift (y := stableRestriction y) hm
    (by simp [stableRestriction]) hu' hw' (Pi.single 0 1)
  have hd' : |entranceStablePartial y 0 - 1| ≤ 66000 * b ^ 2 * Real.exp (512 * b) := by
    rw [entranceStablePartial, entranceStablePhase_fderiv hm hu' hw', hvec]
    have hz : (![0, 0] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
    simp [stableVariationCenterBudget, stableRestriction_apply, Pi.norm_single, hz] at hd
    rw [stableRestriction_apply]
    convert! hd using 1
    ring
  have he : Real.exp (512 * b) ≤ 2 :=
    (Real.exp_bound_div_one_sub_of_interval (by positivity) (by linarith)).trans
      ((div_le_iff₀ (by linarith : 0 < 1 - 512 * b)).mpr (by linarith))
  constructor
  · apply hval.trans
    apply (div_le_iff₀ (by linarith : 0 < y 0 + 1)).mpr
    nlinarith only [hb2, hm]
  · have H := mul_le_mul hb2 he (Real.exp_pos _).le (by positivity : (0 : ℝ) ≤ (1 / 5000) ^ 2)
    nlinarith only [hd', H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceRegion_stable_radial_bounds {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    (k / 2 ≤ entranceStablePhase y - 1 ∧ entranceStablePhase y - 1 ≤ 3 * k / 2) ∧
      (k / 2 ≤ entranceStableRadius y ∧ entranceStableRadius y ≤ 2 * k) ∧
      (1 / 2 ≤ entranceStablePartial y 0 ∧ entranceStablePartial y 0 ≤ 3 / 2) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| ≤ 1 / 10000 := by rw [abs_of_nonneg hy.2.2.1.1]; exact hy.2.2.1.2
  have hw : |y 3| ≤ 1 / 10000 := by rw [abs_of_nonneg hy.2.2.2.2.1]; exact hy.2.2.2.2.2
  obtain ⟨hP, hdP⟩ := entranceStablePhase_small_wall_bounds hm hu hw
  obtain ⟨hPl, hPu⟩ := abs_le.mp hP
  obtain ⟨hdl, hdu⟩ := abs_le.mp hdP
  have hchi : k / 2 ≤ entranceStablePhase y - 1 ∧ entranceStablePhase y - 1 ≤ 3 * k / 2 := by
    obtain ⟨hl, hu⟩ := entranceRegion_phase hk hy
    constructor <;> linarith
  have hpos : 0 ≤ entranceStablePhase y - 1 := by linarith [hchi.1]
  have hRlo : k / 2 ≤ entranceStableRadius y := hchi.1.trans (phaseNorm_ge hpos)
  have hsq := pow_le_pow_left₀ hpos hchi.2 2
  have hv2 : y 2 ^ 2 ≤ 1 := by nlinarith [hy.2.2.2.1.1, hy.2.2.2.1.2]
  have hRhi : entranceStableRadius y ≤ 2 * k := by
    nlinarith only [entranceStableRadius_sq y, hsq, hv2, hRlo, hk, sq_nonneg (k - 1)]
  exact ⟨hchi, ⟨hRlo, hRhi⟩, ⟨by linarith, by linarith⟩⟩

end
end

section
noncomputable section
open BianchiIX

local instance  : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance  : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
private theorem BianchiIX.contDiffAt_entranceStablePartial_one {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (i : Fin 4) :
    ContDiffAt ℝ 1 (fun z => entranceStablePartial z i) y :=
  ((contDiffAt_entranceStablePhase_two hm hu hw).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffAt_const

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceRadialDifferential_apply (y v : ProjectiveState) :
    entranceRadialDifferential y v = ![fderiv ℝ entranceStableRadius y v, v 1, v 2, v 3] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceRadialInverseDifferential_apply (y v : ProjectiveState) :
    entranceRadialInverseDifferential y v =
      ![entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * v 0 -
        entranceStablePartial y 1 / entranceStablePartial y 0 * v 1 -
        y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * v 2 -
        entranceStablePartial y 3 / entranceStablePartial y 0 * v 3, v 1, v 2, v 3] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_entranceRadialCoordinates_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    ContDiffAt ℝ 2 entranceRadialCoordinates y := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_entranceStableRadius_two hm hu hw hv
  · dsimp [entranceRadialCoordinates]; fun_prop
  · dsimp [entranceRadialCoordinates]; fun_prop
  · dsimp [entranceRadialCoordinates]; fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_entranceRadialCoordinates {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    HasFDerivAt entranceRadialCoordinates (entranceRadialDifferential y) y := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact ((contDiffAt_entranceStableRadius_two hm hu hw hv).differentiableAt (by norm_num)).hasFDerivAt
  · exact hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y
  · exact hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y
  · exact hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceRadialDifferential_formula {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2)
    (v : ProjectiveState) :
    entranceRadialDifferential y v =
      ![((entranceStablePhase y - 1) * (entranceStablePartial y 0 * v 0 +
        entranceStablePartial y 1 * v 1 + entranceStablePartial y 3 * v 3) + y 2 * v 2) /
        entranceStableRadius y, v 1, v 2, v 3] := by
  rw [entranceRadialDifferential_apply, entranceStableRadius_fderiv hm hu hw hv,
    entranceStablePhase_fderiv_coordinates hm hu hw]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceRadialDifferential_inverse {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2)
    (hchi : entranceStablePhase y - 1 ≠ 0) (hPM : entranceStablePartial y 0 ≠ 0) :
    Function.LeftInverse (entranceRadialInverseDifferential y) (entranceRadialDifferential y) ∧
      Function.RightInverse (entranceRadialInverseDifferential y) (entranceRadialDifferential y) := by
  have hr := (entranceStableRadius_pos hv).ne'
  constructor
  · intro v
    rw [entranceRadialDifferential_formula hm hu hw hv, entranceRadialInverseDifferential_apply]
    ext i
    fin_cases i
    · dsimp
      field_simp
      ring
    · rfl
    · rfl
    · rfl
  · intro v
    rw [entranceRadialDifferential_formula hm hu hw hv, entranceRadialInverseDifferential_apply]
    ext i
    fin_cases i
    · dsimp
      field_simp
      ring
    · rfl
    · rfl
    · rfl

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.exists_entranceRadialInverseAt {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2)
    (hchi : entranceStablePhase y - 1 ≠ 0) (hPM : entranceStablePartial y 0 ≠ 0) :
    ∃ Ψ, EntranceRadialInverseAt y Ψ := by
  have H := entranceRadialDifferential_inverse hm hu hw hv hchi hPM
  let E : ProjectiveState ≃L[ℝ] ProjectiveState := ContinuousLinearEquiv.equivOfInverse
    (entranceRadialDifferential y) (entranceRadialInverseDifferential y) H.1 H.2
  have hc := contDiffAt_entranceRadialCoordinates_two hm hu hw hv
  have hd : HasFDerivAt entranceRadialCoordinates (E : ProjectiveState →L[ℝ] ProjectiveState) y :=
    hasFDerivAt_entranceRadialCoordinates hm hu hw hv
  have hs := hc.hasStrictFDerivAt' hd (by norm_num)
  refine ⟨hc.localInverse hd (by norm_num), ?_⟩
  exact ⟨hc.localInverse_apply_image hd (by norm_num), hc.to_localInverse hd (by norm_num),
    hs.to_localInverse.hasFDerivAt, hs.eventually_left_inverse, hs.eventually_right_inverse⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.exists_entranceRegion_radial_inverse {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ∃ Ψ, EntranceRadialInverseAt y Ψ := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  exact exists_entranceRadialInverseAt hm hu hw hv (by linarith [hchi.1]) (by linarith [hPM.1])

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.scalar_differential {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) {f : ProjectiveState → ℝ} (hf : DifferentiableAt ℝ f y)
    (v : ProjectiveState) :
    fderiv ℝ (fun z => f (Ψ z)) (entranceRadialCoordinates y) v =
      fderiv ℝ f y (entranceRadialInverseDifferential y v) := by
  have hd : HasFDerivAt f (fderiv ℝ f y) (Ψ (entranceRadialCoordinates y)) := by
    rw [H.apply_base]
    exact hf.hasFDerivAt
  exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) (hd.comp _ H.hasFDerivAt).fderiv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceWallLogRates_field {y : ProjectiveState} (hD : entranceClockRate y ≠ 0) :
    projectiveField y 1 = entranceClockRate y * entranceStrongLogRate y * y 1 ∧
      projectiveField y 3 = entranceClockRate y * entranceWeakLogRate y * y 3 := by
  have hn : connectionSpeed (y 0) (y 1) (y 2) (y 3) ≠ 0 := hD
  constructor
  · change strongVelocity _ _ _ _ = _
    unfold entranceClockRate entranceStrongLogRate connectionStrongClockRate strongVelocity connectionStrongRate
    field_simp
  · change weakVelocity _ _ _ _ = _
    unfold entranceClockRate entranceWeakLogRate connectionWeakClockRate weakVelocity
    field_simp
    unfold connectionSpeed
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_entranceWallLogRates (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : entranceClockRate y ≠ 0) :
    ContDiffAt ℝ n entranceStrongLogRate y ∧ ContDiffAt ℝ n entranceWeakLogRate y := by
  unfold entranceClockRate connectionSpeed coupling at hD
  constructor
  · unfold entranceStrongLogRate connectionStrongClockRate connectionStrongRate connectionSpeed coupling
    fun_prop (disch := assumption)
  · unfold entranceWeakLogRate connectionWeakClockRate connectionSpeed coupling
    fun_prop (disch := assumption)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.entranceRadialDrift_eq_log_rate {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    entranceRadialDrift y = fderiv ℝ entranceStableRadius y (projectiveField y) / entranceClockRate y :=
  (entranceStableRadius_log_rate hm hu hw hv).symm

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.entranceRadialDrift_lie_eventuallyEq {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    (fun z => fderiv ℝ entranceStableRadius z (entranceLogField z)) =ᶠ[𝓝 y] entranceRadialDrift := by
  have hm : 2 < y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  filter_upwards [(continuous_apply 0).continuousAt.eventually (isOpen_Ioi.mem_nhds hm),
    (continuous_apply 1).abs.continuousAt.eventually (isOpen_Iio.mem_nhds hu),
    (continuous_apply 3).abs.continuousAt.eventually (isOpen_Iio.mem_nhds hw),
    (continuous_apply 2).continuousAt.eventually (isOpen_Ioi.mem_nhds hv)] with z hmz huz hwz hvz
  rw [entranceRadialDrift_eq_log_rate hmz.le huz hwz hvz, entranceLogField, map_smul]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_entranceRadialDrift_one {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContDiffAt ℝ 1 entranceRadialDrift y := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hR := (contDiffAt_entranceStableRadius_two hm hu hw hv).fderiv_right (m := 1) (by norm_num)
  exact (hR.clm_apply (contDiffAt_entranceLogField 1 (entranceRegion_clock_pos hk hy).ne')).congr_of_eventuallyEq
    (entranceRadialDrift_lie_eventuallyEq hk hy hv).symm

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_entranceRadialTangent {Y v : ℝ → ProjectiveState} {a t k : ℝ}
    (hY : HasDerivAt Y (a • entranceLogField (Y t)) t)
    (hv : HasDerivAt v (a • fderiv ℝ entranceLogField (Y t) (v t)) t)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k (Y t)) (hV : 0 < Y t 2) :
    HasDerivAt (fun s => fderiv ℝ entranceStableRadius (Y s) (v s))
      (a * fderiv ℝ entranceRadialDrift (Y t) (v t)) t := by
  have hm : 2 ≤ Y t 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |Y t 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |Y t 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have H := hasDerivAt_scaled_observable_variation (contDiffAt_entranceStableRadius_two hm hu hw hV)
    ((contDiffAt_entranceLogField 1 (entranceRegion_clock_pos hk hy).ne').differentiableAt (by norm_num)) hY hv
  rwa [(entranceRadialDrift_lie_eventuallyEq hk hy hV).fderiv_eq] at H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.entranceRadialDrift_tangent_decomposition {y v : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) (hactive : v 2 = 0) :
    fderiv ℝ entranceRadialDrift y v =
      entranceRadialVariationCoefficients y 0 * fderiv ℝ entranceStableRadius y v +
      entranceRadialVariationCoefficients y 1 * (v 1 / y 1) +
      entranceRadialVariationCoefficients y 2 * (v 3 / y 3) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu' : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw' : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hinv := (entranceRadialDifferential_inverse hm hu' hw' hv
    (by linarith [hchi.1]) (by linarith [hPM.1])).1 v
  rw [entranceRadialDifferential_apply, hactive] at hinv
  let Z := fderiv ℝ entranceStableRadius y v
  have he : (![Z, v 1, 0, v 3] : ProjectiveState) =
      Z • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 3 • Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp
  have hd : fderiv ℝ entranceRadialDrift y v = entranceRadialDriftDifferential y ![Z, v 1, 0, v 3] := by
    change _ = fderiv ℝ entranceRadialDrift y (entranceRadialInverseDifferential y _)
    rw [hinv]
  rw [hd, he]
  simp only [map_add, map_smul, smul_eq_mul]
  dsimp [entranceRadialVariationCoefficients]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_entranceProjectedRadialTangent {y : ProjectiveState} {t₀ t k : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hk : 7 / 4 ≤ k) (hreg : entranceRegion k (projectiveOriginalFlow y t₀ t))
    (hv : 0 < projectiveOriginalFlow y t₀ t 2)
    (hu : projectiveOriginalFlow y t₀ t 1 ≠ 0) (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0)
    (w : ProjectiveState) (hw0 : w 2 = 0) :
    let Y := projectiveOriginalFlow y t₀
    let v := fun s => entranceProjectedFlowVariation y t₀ s w
    let Z := fun s => fderiv ℝ entranceStableRadius (Y s) (v s)
    let c := entranceRadialVariationCoefficients (Y t)
    HasDerivAt Z (entranceOriginalClockRate (Y t) *
      (c 0 * Z t + c 1 * (v t 1 / Y t 1) + c 2 * (v t 3 / Y t 3))) t := by
  dsimp only
  have hclock := (entranceRegion_clock_pos hk hreg).ne'
  have hY := hasDerivAt_projectiveOriginalFlow_time hD ht hA
  rw [projectiveOriginalField_entranceLog hclock] at hY
  have H := hasDerivAt_entranceRadialTangent hY
    (hasDerivAt_entranceProjectedFlowVariation hD ht hA hv.ne' hclock w) hk hreg hv
  have hactive : entranceProjectedFlowVariation y t₀ t w 2 = 0 := by
    rw [entranceProjectedFlowVariation_active hv.ne' hclock w, hw0, zero_div, zero_mul]
  rwa [entranceRadialDrift_tangent_decomposition hk hreg hv hu hw hactive] at H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.EntranceRadialInverseAt.wallLogDifferential_eq {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    fderiv ℝ (fun z => entranceStrongLogRate (Ψ z)) (entranceRadialCoordinates y) = entranceStrongLogDifferential y ∧
      fderiv ℝ (fun z => entranceWeakLogRate (Ψ z)) (entranceRadialCoordinates y) = entranceWeakLogDifferential y := by
  obtain ⟨hs, hw⟩ := contDiffAt_entranceWallLogRates 1 (entranceRegion_clock_pos hk hy).ne'
  constructor
  · ext v
    exact H.scalar_differential (hs.differentiableAt (by norm_num)) v
  · ext v
    exact H.scalar_differential (hw.differentiableAt (by norm_num)) v

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuousAt_entranceWallLogDifferential_apply {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (v : ProjectiveState) :
    ContinuousAt (fun y => entranceStrongLogDifferential y v) y ∧
      ContinuousAt (fun y => entranceWeakLogDifferential y v) y := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).continuousAt
  have hR := (contDiffAt_entranceStableRadius_two hm hu hw hv).continuousAt
  have hpartial (i : Fin 4) := (contDiffAt_entranceStablePartial_one hm hu hw i).continuousAt
  have hbounds := entranceRegion_stable_radial_bounds hk hy
  have hchi : entranceStablePhase y - 1 ≠ 0 := by linarith [hbounds.1.1]
  have hPM : entranceStablePartial y 0 ≠ 0 := by linarith [hbounds.2.2.1]
  have hden := mul_ne_zero hchi hPM
  have hInv : ContinuousAt (fun z => entranceRadialInverseDifferential z v) y := by
    simp only [entranceRadialInverseDifferential_apply]
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact ((((hR.div ((hP.sub_const 1).mul (hpartial 0)) hden).mul_const (v 0)).sub
        (((hpartial 1).div (hpartial 0) hPM).mul_const (v 1))).sub
        (((continuousAt_apply 2 y).div ((hP.sub_const 1).mul (hpartial 0)) hden).mul_const (v 2))).sub
        (((hpartial 3).div (hpartial 0) hPM).mul_const (v 3))
    all_goals exact continuousAt_const
  obtain ⟨hs, hw'⟩ := contDiffAt_entranceWallLogRates 1 (entranceRegion_clock_pos hk hy).ne'
  exact ⟨(hs.continuousAt_fderiv (by norm_num)).clm_apply hInv,
    (hw'.continuousAt_fderiv (by norm_num)).clm_apply hInv⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuousAt_entranceRadialInverseDifferential_apply {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (v : ProjectiveState) :
    ContinuousAt (fun z => entranceRadialInverseDifferential z v) y := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).continuousAt
  have hR := (contDiffAt_entranceStableRadius_two hm hu hw hv).continuousAt
  have hpartial (i : Fin 4) := (contDiffAt_entranceStablePartial_one hm hu hw i).continuousAt
  have hbounds := entranceRegion_stable_radial_bounds hk hy
  have hchi : entranceStablePhase y - 1 ≠ 0 := by linarith [hbounds.1.1]
  have hPM : entranceStablePartial y 0 ≠ 0 := by linarith [hbounds.2.2.1]
  have hden := mul_ne_zero hchi hPM
  simp only [entranceRadialInverseDifferential_apply]
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact ((((hR.div ((hP.sub_const 1).mul (hpartial 0)) hden).mul_const (v 0)).sub
      (((hpartial 1).div (hpartial 0) hPM).mul_const (v 1))).sub
      (((continuousAt_apply 2 y).div ((hP.sub_const 1).mul (hpartial 0)) hden).mul_const (v 2))).sub
      (((hpartial 3).div (hpartial 0) hPM).mul_const (v 3))
  all_goals exact continuousAt_const

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuousAt_entranceRadialDriftDifferential_apply {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (v : ProjectiveState) :
    ContinuousAt (fun z => entranceRadialDriftDifferential z v) y :=
  ((contDiffAt_entranceRadialDrift_one hk hy hv).continuousAt_fderiv (by norm_num)).clm_apply
    (continuousAt_entranceRadialInverseDifferential_apply hk hy hv v)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.continuousAt_entranceRadialVariationCoefficients {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContinuousAt entranceRadialVariationCoefficients y := by
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact continuousAt_entranceRadialDriftDifferential_apply hk hy hv (Pi.single 0 1)
  · exact (continuousAt_apply 1 y).mul (continuousAt_entranceRadialDriftDifferential_apply hk hy hv (Pi.single 1 1))
  · exact (continuousAt_apply 3 y).mul (continuousAt_entranceRadialDriftDifferential_apply hk hy hv (Pi.single 3 1))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_entranceWallRadialSource_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ContinuousAt (entranceWallRadialSource k) y ∧ ‖entranceWallRadialSource k y‖ ≤ C := by
  obtain ⟨C, hC, HC⟩ := exists_entranceWallLogRates_weighted_bounds
  refine ⟨C, hC, ?_⟩
  intro k y hk hy hv
  obtain ⟨hs, hw⟩ := continuousAt_entranceWallLogDifferential_apply hk hy hv (Pi.single 0 1)
  obtain ⟨Ψ, H⟩ := exists_entranceRegion_radial_inverse hk hy hv
  have hb := (HC k y hk hy hv Ψ H).1
  obtain ⟨hA, hB⟩ := H.wallLogDifferential_eq hk hy
  rw [hA, hB] at hb
  constructor
  · apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact hs
    · exact hw.const_mul _
  · apply (pi_norm_le_iff_of_nonneg hC.le).mpr
    intro i
    fin_cases i
    · change |entranceStrongLogDifferential y (Pi.single 0 1)| ≤ C
      exact (le_add_of_nonneg_right (mul_nonneg (sq_nonneg k) (abs_nonneg _))).trans hb
    · change |k ^ 2 * entranceWeakLogDifferential y (Pi.single 0 1)| ≤ C
      rw [abs_mul, abs_of_nonneg (sq_nonneg k)]
      exact (le_add_of_nonneg_left (abs_nonneg _)).trans hb

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_scaled_entrance_wall_radial_response :
    ∃ C > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k : ℝ),
      7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
      ∀ (f : ℝ → (Fin 2 → ℝ)) (Z : ℝ → ℝ), ContinuousOn Z (Icc b c) →
      (∀ r ∈ Icc b c, HasDerivAt f
        (((a r * entranceClockRate (Y r)) • entranceWallWeightedMatrix k (Y r)).mulVec (f r) +
          ((a r * entranceClockRate (Y r)) * Z r) • entranceWallRadialSource k (Y r)) r) →
      |f c 0 - f b 0| + |f c 1 - f b 1| ≤ C * (Y s 1 * |f b 0| + Y s 3 / k ^ 2 * |f b 1| +
        ∫ r in b..c, |Z r| * (a r * entranceClockRate (Y r))) := by
  obtain ⟨K, hK, HK⟩ := exists_scaled_entrance_wall_solution_growth
  obtain ⟨J, hJ, HJ⟩ := exists_entranceWallRadialSource_bounds
  refine ⟨2 * K * (J + 1), by positivity, ?_⟩
  intro Y a s t k hk hst hY hac ha hy hv b c hsb hbc hct f Z hZ hf
  have hsub : Icc b c ⊆ Icc s t := fun r hr => ⟨hsb.trans hr.1, hr.2.trans hct⟩
  let q := fun r => a r * entranceClockRate (Y r)
  let p := fun r => (q r * Z r) • entranceWallRadialSource k (Y r)
  have hq (r : ℝ) (hr : r ∈ Icc b c) : 0 ≤ q r :=
    mul_nonneg (ha r (hsub hr)) (entranceRegion_clock_pos hk (hy r (hsub hr))).le
  have hqc : ContinuousOn q (Icc b c) := (hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))).mono hsub
  have hsource : ContinuousOn (fun r => entranceWallRadialSource k (Y r)) (Icc b c) := by
    intro r hr
    exact (((HJ k (Y r) hk (hy r (hsub hr)) (hv r (hsub hr))).1).comp
      (hY r (hsub hr)).continuousAt).continuousWithinAt
  have hp : ContinuousOn p (Icc b c) := (hqc.mul hZ).smul hsource
  have hpoint (r : ℝ) (hr : r ∈ Icc b c) : ‖p r‖ ≤ J * (|Z r| * q r) := by
    simp only [p, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq r hr)]
    exact (mul_le_mul_of_nonneg_left (HJ k (Y r) hk (hy r (hsub hr)) (hv r (hsub hr))).2
      (mul_nonneg (hq r hr) (abs_nonneg _))).trans_eq (by ring)
  have hP : (∫ r in b..c, ‖p r‖) ≤ J * ∫ r in b..c, |Z r| * q r := by
    have H := intervalIntegral.integral_mono_on (μ := volume) hbc (hp.norm.intervalIntegrable_of_Icc hbc)
      (((hZ.abs.mul hqc).const_mul J).intervalIntegrable_of_Icc hbc) hpoint
    simpa only [intervalIntegral.integral_const_mul, Pi.mul_apply] using H
  have hI0 : 0 ≤ ∫ r in b..c, |Z r| * q r :=
    intervalIntegral.integral_nonneg hbc (fun r hr => mul_nonneg (abs_nonneg _) (hq r hr))
  let B := Y s 1 * |f b 0| + Y s 3 / k ^ 2 * |f b 1|
  have hB : 0 ≤ B := by
    have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
    exact add_nonneg (mul_nonneg (hy s hs).2.2.1.1 (abs_nonneg _))
      (mul_nonneg (div_nonneg (hy s hs).2.2.2.2.1 (sq_nonneg k)) (abs_nonneg _))
  have HG := HK Y a s t k hk hst hY hac ha hy hv b c hsb hbc hct f p hp hf
  have HD : ‖f c - f b‖ ≤ K * (J + 1) * (B + ∫ r in b..c, |Z r| * q r) := by
    apply HG.trans ((mul_le_mul_of_nonneg_left (add_le_add (le_refl B) hP) hK.le).trans ?_)
    have HB : B + J * (∫ r in b..c, |Z r| * q r) ≤ (J + 1) * (B + ∫ r in b..c, |Z r| * q r) := by
      nlinarith only [mul_nonneg hJ.le hB, hI0]
    exact (mul_le_mul_of_nonneg_left HB hK.le).trans_eq (by ring)
  have hv' (i : Fin 2) : |f c i - f b i| ≤ ‖f c - f b‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (f c - f b) i
  exact (add_le_add (hv' 0) (hv' 1)).trans (by nlinarith only [HD])

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.entranceLogField_wall_rates {y : ProjectiveState} (hD : entranceClockRate y ≠ 0) :
    entranceLogField y 1 = entranceStrongLogRate y * y 1 ∧
      entranceLogField y 3 = entranceWeakLogRate y * y 3 := by
  obtain ⟨hs, hw⟩ := entranceWallLogRates_field hD
  constructor
  · change (entranceClockRate y)⁻¹ * projectiveField y 1 = _
    rw [hs]
    field_simp
  · change (entranceClockRate y)⁻¹ * projectiveField y 3 = _
    rw [hw]
    field_simp

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.entranceLogField_wall_fderiv {y : ProjectiveState}
    (hD : entranceClockRate y ≠ 0) (v : ProjectiveState) :
    fderiv ℝ entranceLogField y v 1 =
        fderiv ℝ entranceStrongLogRate y v * y 1 + entranceStrongLogRate y * v 1 ∧
      fderiv ℝ entranceLogField y v 3 =
        fderiv ℝ entranceWeakLogRate y v * y 3 + entranceWeakLogRate y * v 3 := by
  have hF := ((contDiffAt_entranceLogField 1 hD).differentiableAt (by norm_num)).hasFDerivAt
  have hnear := continuous_entranceClockRate.continuousAt.eventually_ne hD
  have H (i : Fin 4) (b : ProjectiveState → ℝ) (hb : DifferentiableAt ℝ b y)
      (he : (fun z => entranceLogField z i) =ᶠ[𝓝 y] (fun z => b z * z i)) :
      fderiv ℝ entranceLogField y v i = fderiv ℝ b y v * y i + b y * v i := by
    have hf := (hasFDerivAt_apply (𝕜 := ℝ) i (entranceLogField y)).comp y hF
    have hg := (hb.hasFDerivAt.mul (hasFDerivAt_apply (𝕜 := ℝ) i y)).congr_of_eventuallyEq he
    have hd := congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) (hf.unique hg)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      add_apply, smul_apply, smul_eq_mul, mul_comm, add_comm] using hd
  obtain ⟨hs, hw⟩ := contDiffAt_entranceWallLogRates 1 hD
  constructor
  · apply H 1 entranceStrongLogRate (hs.differentiableAt (by norm_num))
    filter_upwards [hnear] with z hz
    exact (entranceLogField_wall_rates hz).1
  · apply H 3 entranceWeakLogRate (hw.differentiableAt (by norm_num))
    filter_upwards [hnear] with z hz
    exact (entranceLogField_wall_rates hz).2

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_relative_variation {u v : ℝ → ℝ} {a b c t : ℝ}
    (hu : HasDerivAt u (a * b * u t) t)
    (hv : HasDerivAt v (a * (c * u t + b * v t)) t) (hne : u t ≠ 0) :
    HasDerivAt (fun s => v s / u s) (a * c) t := by
  apply (hv.div hu hne).congr_deriv
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_entranceWallTangent {Y v : ℝ → ProjectiveState} {a t k : ℝ}
    (hY : HasDerivAt Y (a • entranceLogField (Y t)) t)
    (hv : HasDerivAt v (a • fderiv ℝ entranceLogField (Y t) (v t)) t)
    (hu : Y t 1 ≠ 0) (hw : Y t 3 ≠ 0) (hD : entranceClockRate (Y t) ≠ 0) :
    HasDerivAt (fun s => entranceWallTangent k (Y s) (v s))
      (a • ![fderiv ℝ entranceStrongLogRate (Y t) (v t),
        k ^ 2 * fderiv ℝ entranceWeakLogRate (Y t) (v t)]) t := by
  obtain ⟨hs, hw'⟩ := entranceLogField_wall_rates hD
  obtain ⟨hds, hdw⟩ := entranceLogField_wall_fderiv hD (v t)
  have hY1 := hasDerivAt_pi.mp hY 1
  have hY3 := hasDerivAt_pi.mp hY 3
  have hv1 := hasDerivAt_pi.mp hv 1
  have hv3 := hasDerivAt_pi.mp hv 3
  simp only [Pi.smul_apply, smul_eq_mul, hs] at hY1
  simp only [Pi.smul_apply, smul_eq_mul, hw'] at hY3
  simp only [Pi.smul_apply, smul_eq_mul, hds] at hv1
  simp only [Pi.smul_apply, smul_eq_mul, hdw] at hv3
  have H1 := hasDerivAt_relative_variation (u := fun s => Y s 1) (v := fun s => v s 1)
    (a := a) (b := entranceStrongLogRate (Y t))
    (by simpa only [mul_assoc] using hY1) hv1 hu
  have H3 := (hasDerivAt_relative_variation (u := fun s => Y s 3) (v := fun s => v s 3)
    (a := a) (b := entranceWeakLogRate (Y t))
    (by simpa only [mul_assoc] using hY3) hv3 hw).const_mul (k ^ 2)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact H1
  · convert! H3 using 1
    change a * (k ^ 2 * _) = k ^ 2 * (a * _)
    ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.entranceWallTangent_radial_decomposition {y v : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) (hactive : v 2 = 0) :
    ![fderiv ℝ entranceStrongLogRate y v, k ^ 2 * fderiv ℝ entranceWeakLogRate y v] =
      (entranceWallWeightedMatrix k y).mulVec (entranceWallTangent k y v) +
        (fderiv ℝ entranceStableRadius y v) • entranceWallRadialSource k y := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu' : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw' : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hinv := (entranceRadialDifferential_inverse hm hu' hw' hv
    (by linarith [hchi.1]) (by linarith [hPM.1])).1 v
  rw [entranceRadialDifferential_apply, hactive] at hinv
  let Z := fderiv ℝ entranceStableRadius y v
  have he : (![Z, v 1, 0, v 3] : ProjectiveState) =
      Z • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 3 • Pi.single 3 1 := by
    ext i
    fin_cases i <;> simp
  have hs : fderiv ℝ entranceStrongLogRate y v =
      entranceStrongLogDifferential y ![Z, v 1, 0, v 3] := by
    change _ = fderiv ℝ entranceStrongLogRate y (entranceRadialInverseDifferential y _)
    rw [hinv]
  have hw'' : fderiv ℝ entranceWeakLogRate y v =
      entranceWeakLogDifferential y ![Z, v 1, 0, v 3] := by
    change _ = fderiv ℝ entranceWeakLogRate y (entranceRadialInverseDifferential y _)
    rw [hinv]
  rw [hs, hw'', he]
  simp only [map_add, map_smul, smul_eq_mul]
  have hk0 : k ≠ 0 := by linarith
  ext i
  fin_cases i <;>
    simp [entranceWallWeightedMatrix, entranceWallTangent, entranceWallRadialSource, Z] <;>
      field_simp <;> ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_entranceProjectedWallTangent {y : ProjectiveState} {t₀ t k : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hk : 7 / 4 ≤ k) (hreg : entranceRegion k (projectiveOriginalFlow y t₀ t))
    (hv : 0 < projectiveOriginalFlow y t₀ t 2)
    (hu : projectiveOriginalFlow y t₀ t 1 ≠ 0) (hw : projectiveOriginalFlow y t₀ t 3 ≠ 0)
    (w : ProjectiveState) (hw0 : w 2 = 0) :
    let Y := projectiveOriginalFlow y t₀
    let v := fun s => entranceProjectedFlowVariation y t₀ s w
    let f := fun s => entranceWallTangent k (Y s) (v s)
    let q := entranceOriginalClockRate (Y t)
    HasDerivAt f (((q • entranceWallWeightedMatrix k (Y t)).mulVec (f t)) +
      (q * fderiv ℝ entranceStableRadius (Y t) (v t)) • entranceWallRadialSource k (Y t)) t := by
  dsimp only
  have hclock := (entranceRegion_clock_pos hk hreg).ne'
  have hY := hasDerivAt_projectiveOriginalFlow_time hD ht hA
  rw [projectiveOriginalField_entranceLog hclock] at hY
  have H := hasDerivAt_entranceWallTangent (k := k) hY
    (hasDerivAt_entranceProjectedFlowVariation hD ht hA hv.ne' hclock w) hu hw hclock
  have hactive : entranceProjectedFlowVariation y t₀ t w 2 = 0 := by
    rw [entranceProjectedFlowVariation_active hv.ne' hclock w, hw0, zero_div, zero_mul]
  rw [entranceWallTangent_radial_decomposition hk hreg hv hu hw hactive] at H
  simpa only [smul_add, smul_smul, Matrix.smul_mulVec] using H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_actual_entrance_wall_response :
    ∃ C > (0 : ℝ), ∀ (y : ProjectiveState) (t₀ s t k : ℝ),
      0 < projectiveStateDenom y → 7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, r ∈ normalizedMaxDomain (fromProjectiveState y) t₀) →
      (∀ r ∈ Icc s t, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ r 0) →
      let Y := projectiveOriginalFlow y t₀
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      (∀ r ∈ Icc s t, Y r 1 ≠ 0 ∧ Y r 3 ≠ 0) →
      ∀ (w : ProjectiveState), w 2 = 0 →
      let v := fun r => entranceProjectedFlowVariation y t₀ r w
      let f := fun r => entranceWallTangent k (Y r) (v r)
      let Z := fun r => fderiv ℝ entranceStableRadius (Y r) (v r)
      ∀ b c : ℝ, s ≤ b → b ≤ c → c ≤ t →
      |f c 0 - f b 0| + |f c 1 - f b 1| ≤ C * (Y s 1 * |f b 0| + Y s 3 / k ^ 2 * |f b 1| +
        ∫ r in b..c, |Z r| * entranceOriginalClockRate (Y r)) := by
  obtain ⟨C, hC, HC⟩ := exists_scaled_entrance_wall_radial_response
  refine ⟨C, hC, ?_⟩
  intro y t₀ s t k hD hk hst hdom hA Y hreg hv hwall w hw0 v f Z b c hsb hbc hct
  let a := fun r => 6 / projectiveStateDenom (Y r)
  have hden (r : ℝ) (hr : r ∈ Icc s t) : 0 < projectiveStateDenom (Y r) := by
    have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ r) = 1 :=
      (normalizedMaxCurve_constraint (hdom r hr)).trans (fromProjectiveState_constraint hD.ne')
    exact toProjectiveState_denom_pos (hA r hr) hc
  have hY (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt Y (a r • projectiveField (Y r)) r :=
    hasDerivAt_projectiveOriginalFlow_time hD (hdom r hr) (hA r hr)
  have hac : ContinuousOn a (Icc s t) := by
    intro r hr
    exact (continuousAt_const.div ((contDiff_projectiveStateDenom 1).continuous.continuousAt.comp
      (hY r hr).continuousAt) (hden r hr).ne').continuousWithinAt
  have ha (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ a r := (div_pos (by norm_num) (hden r hr)).le
  have hsub : Icc b c ⊆ Icc s t := fun r hr => ⟨hsb.trans hr.1, hr.2.trans hct⟩
  have hZ : ContinuousOn Z (Icc b c) := by
    intro r hr
    have hy := hreg r (hsub hr)
    have hm : 2 ≤ Y r 0 := by linarith [(entranceRegion_phase hk hy).1]
    have hu : |Y r 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
    have hw : |Y r 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
    have hR := (contDiffAt_entranceStableRadius_two hm hu hw (hv r (hsub hr))).continuousAt_fderiv (by norm_num)
    have hvc := (hasDerivAt_entranceProjectedFlowVariation hD (hdom r (hsub hr)) (hA r (hsub hr))
      (hv r (hsub hr)).ne' (entranceRegion_clock_pos hk hy).ne' w).continuousAt
    exact ((hR.comp (hY r (hsub hr)).continuousAt).clm_apply hvc).continuousWithinAt
  have hf (r : ℝ) (hr : r ∈ Icc b c) : HasDerivAt f
      (((a r * entranceClockRate (Y r)) • entranceWallWeightedMatrix k (Y r)).mulVec (f r) +
        ((a r * entranceClockRate (Y r)) * Z r) • entranceWallRadialSource k (Y r)) r :=
    hasDerivAt_entranceProjectedWallTangent hD (hdom r (hsub hr)) (hA r (hsub hr)) hk
      (hreg r (hsub hr)) (hv r (hsub hr)) (hwall r (hsub hr)).1 (hwall r (hsub hr)).2 w hw0
  exact HC Y a s t k hk hst hY hac ha hreg hv b c hsb hbc hct f Z hZ hf

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.continuousAt_entranceWeightedPhaseCoefficients {k : ℝ} {y : ProjectiveState}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContinuousAt (entranceWeightedPhaseCoefficients k) y := by
  apply continuousAt_pi.mpr
  intro i
  have H (j : Fin 3) := (continuous_apply j).continuousAt.comp
    (continuousAt_entranceRadialVariationCoefficients hk hy hv)
  fin_cases i
  · exact H 0
  · exact H 1
  · exact (H 2).div_const _

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.entranceWeightedPhaseCoefficients_feedback (k C l : ℝ) (y : ProjectiveState) :
    coupledVariationFeedback C l (entranceWeightedPhaseCoefficients k y) =
      (C + 1) * entrancePhaseFeedbackRate k l y := by
  simp [coupledVariationFeedback, entranceWeightedPhaseCoefficients, entrancePhaseFeedbackRate,
    abs_div, abs_of_nonneg (sq_nonneg k)]

end
end


/-- Uniform fixed-clock phase and wall response of the actual Einstein flow, including phase increments. -/
theorem solution :
    ∃ T > (0 : ℝ), ∃ K > (0 : ℝ), ∃ F > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∀ (y : ProjectiveState) (t₀ s t k θ : ℝ),
      0 < projectiveStateDenom y → 7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, r ∈ normalizedMaxDomain (fromProjectiveState y) t₀) →
      (∀ r ∈ Icc s t, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ r 0) →
      let Y := projectiveOriginalFlow y t₀
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      (∀ r ∈ Icc s t, Y r 1 ≠ 0 ∧ Y r 3 ≠ 0) →
      Y s 1 ≤ ε → Y s 3 ≤ ε →
      (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (Y s 1 + Y s 3) ^ 2 ≤ 1)) →
      ∀ (w : ProjectiveState), w 2 = 0 →
      let v := fun r => entranceProjectedFlowVariation y t₀ r w
      let X := fun r => v r 1 / Y r 1
      let W := fun r => v r 3 / Y r 3
      let Z := fun r => fderiv ℝ entranceStableRadius (Y r) (v r)
      let A := Y s 1 * |X s| + Y s 3 * |W s|
      let I := Y s 1 * Y s 2 * |X s| +
        (Y s 1 * Y s 2 * Y s 3 + θ * (Y s 2 * Y s 3) ^ 2) * |W s|
      let B := K * I / k
      let Λ := F * (Y s 1 * Y s 2 + θ * (Y s 2 * Y s 3) ^ 2) / k ^ 2
      0 ≤ Λ ∧ Λ ≤ 1 / 2 ∧ ∀ r ∈ Icc s t,
        |Z r - Z s| ≤ 2 * B + 2 * Λ * |Z s| ∧
        |Z r| ≤ (1 + 2 * Λ) * |Z s| + 2 * B ∧
        |X r - X s| + k ^ 2 * |W r - W s| ≤
          T * (A + 2 * (Real.log (Y r 2) - Real.log (Y s 2)) * (|Z s| + B)) := by
  obtain ⟨T, hT, HT⟩ := exists_actual_entrance_wall_response
  obtain ⟨K₀, hK₀, HK⟩ := exists_scaled_entrance_phase_source_budget
  obtain ⟨F₀, hF₀, HF⟩ := exists_scaled_entrance_phase_feedback_budget
  let K := K₀ * (1 + 3 * T)
  let F := (T + 1) * F₀
  let ε := min (1 / 10000) (1 / (4 * F))
  have hK : 0 < K := by dsimp [K]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  refine ⟨T, hT, K, hK, F, hF, ε, hε, ?_⟩
  intro y t₀ s t k θ hD hk hst hdom hchart Y hreg hv hwall huε hwε hθ w hw0 v X W Z A I B Λ
  let a := fun r => 6 / projectiveStateDenom (Y r)
  let q := fun r => entranceOriginalClockRate (Y r)
  let l := fun r => Real.log (Y r 2) - Real.log (Y s 2)
  let f := fun r => entranceWallTangent k (Y r) (v r)
  let c := fun r => entranceWeightedPhaseCoefficients k (Y r)
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hθ01 : 0 ≤ θ ∧ θ ≤ 1 := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · exact ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hsmall : 0 ≤ Λ ∧ Λ ≤ 1 / 2 := entrance_phase_feedback_small hF
    ((min_le_left _ _).trans (by norm_num : (1 : ℝ) / 10000 ≤ 1)) (min_le_right _ _) hk1 hθ01
    ⟨(hreg s hs).2.2.1.1, huε⟩ (hreg s hs).2.2.2.1 ⟨(hreg s hs).2.2.2.2.1, hwε⟩
  have hA : 0 ≤ A := by dsimp [A]; positivity [(hreg s hs).2.2.1.1, (hreg s hs).2.2.2.2.1]
  have hB : 0 ≤ B := by
    dsimp [B, I]
    positivity [(hreg s hs).2.2.1.1, (hreg s hs).2.2.2.1.1, (hreg s hs).2.2.2.2.1, hθ01.1]
  have hden (r : ℝ) (hr : r ∈ Icc s t) : 0 < projectiveStateDenom (Y r) := by
    have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ r) = 1 :=
      (normalizedMaxCurve_constraint (hdom r hr)).trans (fromProjectiveState_constraint hD.ne')
    exact toProjectiveState_denom_pos (hchart r hr) hc
  have hY (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt Y (a r • projectiveField (Y r)) r :=
    hasDerivAt_projectiveOriginalFlow_time hD (hdom r hr) (hchart r hr)
  have hac : ContinuousOn a (Icc s t) := by
    intro r hr
    exact (continuousAt_const.div ((contDiff_projectiveStateDenom 1).continuous.continuousAt.comp
      (hY r hr).continuousAt) (hden r hr).ne').continuousWithinAt
  have ha (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ a r := (div_pos (by norm_num) (hden r hr)).le
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hreg r hr)).le
  have hl (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt l (q r) r :=
    (hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne').sub_const _
  have hmono : MonotoneOn l (Icc s t) := monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Icc s t) (HasDerivAt.continuousOn hl)
    (fun r hr => (hl r (interior_subset hr)).hasDerivWithinAt) (fun r hr => hq r (interior_subset hr))
  have hl0 (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ l r := by
    have H := hmono hs hr hr.1
    simpa only [l, sub_self] using H
  have hcc : ContinuousOn c (Icc s t) := by
    intro r hr
    exact ((continuousAt_entranceWeightedPhaseCoefficients hk (hreg r hr) (hv r hr)).comp
      (hY r hr).continuousAt).continuousWithinAt
  have hf0 (r : ℝ) : f r 0 = X r := rfl
  have hf1 (r : ℝ) : f r 1 = k ^ 2 * W r := rfl
  have hdiff (r : ℝ) : |f r 0 - f s 0| + |f r 1 - f s 1| =
      |X r - X s| + k ^ 2 * |W r - W s| := by
    rw [hf0, hf0, hf1, hf1, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg k)]
  have htrans (r : ℝ) (hr : r ∈ Icc s t) :
      |f r 0 - f s 0| + |f r 1 - f s 1| ≤ T * (A + ∫ z in s..r, |Z z| * q z) := by
    have H := HT y t₀ s t k hD hk hst hdom hchart hreg hv hwall w hw0 s r le_rfl hr.1 hr.2
    change _ ≤ T * (Y s 1 * |f s 0| + Y s 3 / k ^ 2 * |f s 1| + _) at H
    have hinit : Y s 1 * |f s 0| + Y s 3 / k ^ 2 * |f s 1| = A := by
      rw [hf0, hf1, abs_mul, abs_of_nonneg (sq_nonneg k)]
      dsimp [A]
      field_simp
    rwa [hinit] at H
  have hsource : (∫ r in s..t, coupledVariationSource T A (f s 0) (f s 1) (c r) * q r) ≤ B := by
    exact HK Y a s t k θ T (X s) (W s) hk hst hT.le hY hac ha hreg hv hθ
  have hbudget : (∫ r in s..t, coupledVariationFeedback T (l r) (c r) * q r) ≤ Λ := by
    simp only [c, entranceWeightedPhaseCoefficients_feedback, mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (HF Y a s t k θ hk hst hY hac ha hreg hv hθ)
      (by positivity : 0 ≤ T + 1)).trans_eq (by dsimp [Λ, F]; ring)
  have hZ (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt Z (q r * (c r 0 * Z r + c r 1 * f r 0 + c r 2 * f r 1)) r := by
    have H := hasDerivAt_entranceProjectedRadialTangent hD (hdom r hr) (hchart r hr) hk
      (hreg r hr) (hv r hr) (hwall r hr).1 (hwall r hr).2 w hw0
    convert! H using 1
    dsimp [c, f, entranceWeightedPhaseCoefficients, entranceWallTangent]
    field_simp
    rfl
  have H := coupled_clock_variation_bounds hst hT.le hA hZ hl (by dsimp [l]; ring)
    hqc hq hcc (fun _ _ => rfl) htrans hsource hbudget (by linarith [hsmall.2])
  have hM : (|Z s| + B) / (1 - Λ) ≤ 2 * (|Z s| + B) := by
    apply (div_le_iff₀ (by linarith [hsmall.2] : 0 < 1 - Λ)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hsmall.2 (add_nonneg (abs_nonneg (Z s)) hB)]
  refine ⟨hsmall.1, hsmall.2, ?_⟩
  intro r hr
  have hinc : |Z r - Z s| ≤ 2 * B + 2 * Λ * |Z s| := by
    have HI := (H r hr).2.1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hM hsmall.1))
    nlinarith only [HI, mul_le_mul_of_nonneg_right hsmall.2 hB]
  refine ⟨hinc, ?_, ?_⟩
  · have HT : |Z r| ≤ |Z r - Z s| + |Z s| := by simpa using abs_add_le (Z r - Z s) (Z s)
    nlinarith only [HT, hinc]
  · rw [← hdiff]
    exact (H r hr).2.2.trans ((mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hM (hl0 r hr))) hT.le).trans_eq (by dsimp [l]; ring))
