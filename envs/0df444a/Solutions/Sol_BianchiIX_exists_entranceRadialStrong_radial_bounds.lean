-- Prove2me | solution 1 for BianchiIX.exists_entranceRadialStrong_radial_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:00:20.710695+00:00
-- url     : https://prove2.me/submissions/6f6aef0d-1064-4b7b-94bd-c324b3902fc9

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
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_projectiveOriginalField
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_entranceStrongRemainder_bounds
import Theorems.Thm_BianchiIX_exists_stableBoundaryProjection_refined_derivatives
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coordinate_variation
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_hasFDerivAt_stableBoundaryProjection_in_band
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_integral_le_of_exp_decay
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
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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

private theorem BianchiIX.entranceRadialStrongCoefficient_decomposition {y : ProjectiveState}
    (hr : entranceStableRadius y ≠ 0) (hD : entranceClockRate y ≠ 0) :
    entranceRadialStrongCoefficient y = -entranceStableRadius y / entranceClockRate y +
      entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) := by
  unfold entranceRadialStrongCoefficient entranceStrongRemainder
  field_simp
  nlinarith only [entranceStableRadius_sq y]

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
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.differential_apply {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) (v : ProjectiveState) :
    fderiv ℝ Ψ (entranceRadialCoordinates y) v =
      ![entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * v 0 -
        entranceStablePartial y 1 / entranceStablePartial y 0 * v 1 -
        y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * v 2 -
        entranceStablePartial y 3 / entranceStablePartial y 0 * v 3, v 1, v 2, v 3] := by
  rw [H.hasFDerivAt.fderiv, entranceRadialInverseDifferential_apply]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.phase_partials {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) :
    let z := entranceRadialCoordinates y
    fderiv ℝ Ψ z (Pi.single 0 1) 0 = entranceStableRadius y /
        ((entranceStablePhase y - 1) * entranceStablePartial y 0) ∧
      fderiv ℝ Ψ z (Pi.single 1 1) 0 = -entranceStablePartial y 1 / entranceStablePartial y 0 ∧
      fderiv ℝ Ψ z (Pi.single 2 1) 0 = -y 2 /
        ((entranceStablePhase y - 1) * entranceStablePartial y 0) ∧
      fderiv ℝ Ψ z (Pi.single 3 1) 0 = -entranceStablePartial y 3 / entranceStablePartial y 0 := by
  simp [H.differential_apply, neg_div]

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
open Filter
open scoped Topology

private theorem BianchiIX.entranceRadialInverseDifferential_columns (y : ProjectiveState) :
    entranceRadialInverseDifferential y (Pi.single 0 1) =
        (entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0)) • Pi.single 0 1 ∧
      entranceRadialInverseDifferential y (Pi.single 1 1) = Pi.single 1 1 -
        (entranceStablePartial y 1 / entranceStablePartial y 0) • Pi.single 0 1 ∧
      entranceRadialInverseDifferential y (Pi.single 2 1) = Pi.single 2 1 -
        (y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0)) • Pi.single 0 1 ∧
      entranceRadialInverseDifferential y (Pi.single 3 1) = Pi.single 3 1 -
        (entranceStablePartial y 3 / entranceStablePartial y 0) • Pi.single 0 1 := by
  repeat' constructor
  all_goals
    rw [entranceRadialInverseDifferential_apply]
    ext i
    fin_cases i <;> simp

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.scalar_partials {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) {f : ProjectiveState → ℝ} (hf : DifferentiableAt ℝ f y) :
    let z := entranceRadialCoordinates y
    let L := fderiv ℝ f y
    fderiv ℝ (fun z => f (Ψ z)) z (Pi.single 0 1) =
        entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * L (Pi.single 0 1) ∧
      fderiv ℝ (fun z => f (Ψ z)) z (Pi.single 1 1) = L (Pi.single 1 1) -
        entranceStablePartial y 1 / entranceStablePartial y 0 * L (Pi.single 0 1) ∧
      fderiv ℝ (fun z => f (Ψ z)) z (Pi.single 2 1) = L (Pi.single 2 1) -
        y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * L (Pi.single 0 1) ∧
      fderiv ℝ (fun z => f (Ψ z)) z (Pi.single 3 1) = L (Pi.single 3 1) -
        entranceStablePartial y 3 / entranceStablePartial y 0 * L (Pi.single 0 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := entranceRadialInverseDifferential_columns y
  simp [H.scalar_differential hf, h0, h1, h2, h3, map_sub, map_smul, smul_eq_mul]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.entranceClockRate_fderiv (y v : ProjectiveState) :
    fderiv ℝ entranceClockRate y v =
      v 0 - (y 2 + y 3 - 2 * y 1) * v 1 - y 1 * v 2 - y 1 * v 3 := by
  have hd (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i y
  have H := ((hd 0).sub_const 1).sub ((hd 1).mul (((hd 2).add (hd 3)).sub (hd 1)))
  change HasFDerivAt entranceClockRate _ y at H
  rw [H.fderiv]
  simp only [Pi.add_apply, Pi.sub_apply, sub_apply, add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.clock_partials {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) :
    let z := entranceRadialCoordinates y
    fderiv ℝ (fun z => entranceClockRate (Ψ z)) z (Pi.single 0 1) =
        entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0) ∧
      fderiv ℝ (fun z => entranceClockRate (Ψ z)) z (Pi.single 1 1) =
        -entranceStablePartial y 1 / entranceStablePartial y 0 - (y 2 + y 3 - 2 * y 1) ∧
      fderiv ℝ (fun z => entranceClockRate (Ψ z)) z (Pi.single 2 1) =
        -y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) - y 1 ∧
      fderiv ℝ (fun z => entranceClockRate (Ψ z)) z (Pi.single 3 1) =
        -entranceStablePartial y 3 / entranceStablePartial y 0 - y 1 := by
  have hf : DifferentiableAt ℝ entranceClockRate y := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  simp [H.scalar_differential hf, entranceClockRate_fderiv, entranceRadialInverseDifferential_apply, neg_div]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.clock_radial_cancellation {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ) :
    entranceStableRadius y *
        fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) (Pi.single 0 1) -
        entranceClockRate y =
      entranceStableRadius y ^ 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) -
        (y 0 - 1) + coupling (y 1) (y 2) (y 3) := by
  rw [H.clock_partials.1]
  unfold entranceClockRate connectionSpeed
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.radius_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ) (v : ProjectiveState) :
    fderiv ℝ (fun z => entranceStableRadius (Ψ z)) (entranceRadialCoordinates y) v = v 0 := by
  have heq : (fun z => entranceStableRadius (Ψ z)) =ᶠ[𝓝 (entranceRadialCoordinates y)] (fun z => z 0) := by
    filter_upwards [H.right_inverse] with z hz
    simpa [entranceRadialCoordinates] using congrArg (fun x : ProjectiveState => x 0) hz
  rw [heq.fderiv_eq, (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) (entranceRadialCoordinates y)).fderiv]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.radial_quotient_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    {f : ProjectiveState → ℝ} (hf : DifferentiableAt ℝ f y)
    (hr0 : entranceStableRadius y ≠ 0) (hD0 : entranceClockRate y ≠ 0) (v : ProjectiveState) :
    fderiv ℝ (fun z => f (Ψ z) / (entranceStableRadius (Ψ z) * entranceClockRate (Ψ z)))
        (entranceRadialCoordinates y) v =
      fderiv ℝ (fun z => f (Ψ z)) (entranceRadialCoordinates y) v /
        (entranceStableRadius y * entranceClockRate y) - f y / (entranceStableRadius y * entranceClockRate y) *
        (v 0 / entranceStableRadius y +
          fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) v / entranceClockRate y) := by
  have hn : DifferentiableAt ℝ f (Ψ (entranceRadialCoordinates y)) := by rw [H.apply_base]; exact hf
  have hd : DifferentiableAt ℝ entranceClockRate (Ψ (entranceRadialCoordinates y)) := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  have hnΨ := hn.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have hdΨ := hd.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have hden : (entranceRadialCoordinates y) 0 * entranceClockRate (Ψ (entranceRadialCoordinates y)) ≠ 0 := by
    rw [H.apply_base]
    exact mul_ne_zero hr0 hD0
  have heq : (fun z => f (Ψ z) / (entranceStableRadius (Ψ z) * entranceClockRate (Ψ z))) =ᶠ[𝓝 (entranceRadialCoordinates y)]
      (fun z => f (Ψ z) / (z 0 * entranceClockRate (Ψ z))) := by
    filter_upwards [H.right_inverse] with z hz
    have hr : entranceStableRadius (Ψ z) = z 0 := by
      simpa [entranceRadialCoordinates] using congrArg (fun x : ProjectiveState => x 0) hz
    rw [hr]
  have hq := hnΨ.hasFDerivAt.mul ((hasFDerivAt_inv hden).comp (entranceRadialCoordinates y)
    ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) (entranceRadialCoordinates y)).mul hdΨ.hasFDerivAt))
  change HasFDerivAt (fun z => f (Ψ z) / (z 0 * entranceClockRate (Ψ z))) _ (entranceRadialCoordinates y) at hq
  rw [heq.fderiv_eq, hq.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, Function.comp_def, Pi.mul_apply, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [H.apply_base]
  simp only [entranceRadialCoordinates, Matrix.cons_val_zero]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.EntranceRadialInverseAt.clock_quotient_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    {f : ProjectiveState → ℝ} (hf : DifferentiableAt ℝ f y)
    (hD0 : entranceClockRate y ≠ 0) (v : ProjectiveState) :
    fderiv ℝ (fun z => f (Ψ z) / entranceClockRate (Ψ z)) (entranceRadialCoordinates y) v =
      fderiv ℝ (fun z => f (Ψ z)) (entranceRadialCoordinates y) v / entranceClockRate y -
        f y * fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) v / entranceClockRate y ^ 2 := by
  have hn : DifferentiableAt ℝ f (Ψ (entranceRadialCoordinates y)) := by rw [H.apply_base]; exact hf
  have hd : DifferentiableAt ℝ entranceClockRate (Ψ (entranceRadialCoordinates y)) := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  have hnΨ := hn.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have hdΨ := hd.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have hden : entranceClockRate (Ψ (entranceRadialCoordinates y)) ≠ 0 := by rw [H.apply_base]; exact hD0
  have hq := hnΨ.hasFDerivAt.mul ((hasFDerivAt_inv hden).comp (entranceRadialCoordinates y) hdΨ.hasFDerivAt)
  change HasFDerivAt (fun z => f (Ψ z) / entranceClockRate (Ψ z)) _ (entranceRadialCoordinates y) at hq
  rw [hq.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply, H.apply_base]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_entranceStable_wall_partial_bounds :
    ∃ C > (0 : ℝ), ∀ y : ProjectiveState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 3| < 1 / 200 →
      |entranceStablePartial y 1| ≤ C / (y 0 + 1) * (|y 1| + |y 3|) ∧
        |entranceStablePartial y 3| ≤ C / (y 0 + 1) * (|y 1| + |y 3|) := by
  obtain ⟨C, hC, HC⟩ := exists_stableBoundaryProjection_refined_derivatives
  refine ⟨C, hC, ?_⟩
  intro y hm hu hw
  have H := (HC (stableRestriction y) hm hu hw).2.1
  have hU : stableRestriction (Pi.single (1 : Fin 4) (1 : ℝ)) = Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [stableRestriction]
  have hW : stableRestriction (Pi.single (3 : Fin 4) (1 : ℝ)) = Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [stableRestriction]
  constructor
  · rw [entranceStablePartial, entranceStablePhase_fderiv hm hu hw, hU]
    simpa [stableRestriction_apply, Pi.norm_single] using H (Pi.single 1 1) (by simp)
  · rw [entranceStablePartial, entranceStablePhase_fderiv hm hu hw, hW]
    simpa [stableRestriction_apply, Pi.norm_single] using H (Pi.single 2 1) (by simp)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_entranceRadialInverse_column_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let z := entranceRadialCoordinates y
        (2 / 3 ≤ fderiv ℝ Ψ z (Pi.single 0 1) 0 ∧ fderiv ℝ Ψ z (Pi.single 0 1) 0 ≤ 8) ∧
          |fderiv ℝ Ψ z (Pi.single 1 1) 0| ≤ C * (y 1 + y 3) / k ∧
          |fderiv ℝ Ψ z (Pi.single 2 1) 0| ≤ 4 * y 2 / k ∧
          |fderiv ℝ Ψ z (Pi.single 3 1) 0| ≤ C * (y 1 + y 3) / k := by
  obtain ⟨C, hC, HC⟩ := exists_entranceStable_wall_partial_bounds
  refine ⟨4 * C, by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, hR, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hchi0 : 0 < entranceStablePhase y - 1 := by linarith [hchi.1]
  have hPM0 : 0 < entranceStablePartial y 0 := by linarith [hPM.1]
  have hden : 0 < (entranceStablePhase y - 1) * entranceStablePartial y 0 := mul_pos hchi0 hPM0
  have hdenlo : k / 4 ≤ (entranceStablePhase y - 1) * entranceStablePartial y 0 := by
    have hprod := mul_le_mul hchi.1 hPM.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hchi0.le
    nlinarith only [hprod]
  have hk0 : 0 < k := by linarith
  have hLk : k / 2 ≤ y 0 + 1 := by linarith [(entranceRegion_phase hk hy).1]
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hwall (a : ℝ) (ha : |a| ≤ C / (y 0 + 1) * (y 1 + y 3)) :
      |(-a) / entranceStablePartial y 0| ≤ 4 * C * (y 1 + y 3) / k := by
    rw [abs_div, abs_neg, abs_of_pos hPM0]
    calc
      _ ≤ |a| / (1 / 2) := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hPM.1
      _ = 2 * |a| := by ring
      _ ≤ 2 * (C / (y 0 + 1) * (y 1 + y 3)) := mul_le_mul_of_nonneg_left ha (by norm_num)
      _ ≤ 2 * (C / (k / 2) * (y 1 + y 3)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC.le (by positivity) hLk) hb) (by norm_num)
      _ = _ := by ring
  have hpartials := HC y hm hu hw
  rw [abs_of_nonneg hy.2.2.1.1, abs_of_nonneg hy.2.2.2.2.1] at hpartials
  obtain ⟨h0, h1, h2, h3⟩ := H.phase_partials
  dsimp only
  rw [h0, h1, h2, h3]
  refine ⟨⟨?_, ?_⟩, hwall _ hpartials.1, ?_, hwall _ hpartials.2⟩
  · apply (le_div_iff₀ hden).mpr
    have hRchi : entranceStablePhase y - 1 ≤ entranceStableRadius y := phaseNorm_ge hchi0.le
    have hprod := mul_le_mul_of_nonneg_left hPM.2 hchi0.le
    nlinarith only [hRchi, hprod]
  · apply (div_le_iff₀ hden).mpr
    linarith [hR.2]
  · rw [abs_div, abs_neg, abs_of_pos hv, abs_of_pos hden]
    calc
      _ ≤ y 2 / (k / 4) := div_le_div_of_nonneg_left hv.le (by positivity) hdenlo
      _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_entranceStrongRemainder_one {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 1 entranceStrongRemainder y := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hpartial := contDiffAt_entranceStablePartial_one hm hu hw
  unfold entranceStrongRemainder
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceRadialStrongCoefficient_split (y : ProjectiveState) :
    entranceRadialStrongCoefficient y = -entranceStableRadius y / entranceClockRate y +
      entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) := by
  by_cases hr : entranceStableRadius y = 0
  · simp [entranceRadialStrongCoefficient, hr]
  by_cases hd : entranceClockRate y = 0
  · simp [entranceRadialStrongCoefficient, hd]
  exact entranceRadialStrongCoefficient_decomposition hr hd

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.EntranceRadialInverseAt.strong_differential {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (v : ProjectiveState) :
    let z := entranceRadialCoordinates y
    let Q := fderiv ℝ (fun z => entranceClockRate (Ψ z)) z
    fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z v =
      (entranceStableRadius y * Q v - entranceClockRate y * v 0) / entranceClockRate y ^ 2 +
      fderiv ℝ (fun z => entranceStrongRemainder (Ψ z)) z v / (entranceStableRadius y * entranceClockRate y) -
      entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) *
        (v 0 / entranceStableRadius y + Q v / entranceClockRate y) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hr := (contDiffAt_entranceStableRadius_two hm hu hw hv).differentiableAt (by norm_num)
  have hE := (contDiffAt_entranceStrongRemainder_one hm hu hw).differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ entranceClockRate y := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  have hr0 := (entranceStableRadius_pos hv).ne'
  have hD0 := (entranceRegion_clock_pos hk hy).ne'
  have hleft : DifferentiableAt ℝ (fun z => entranceStableRadius (Ψ z) / entranceClockRate (Ψ z))
      (entranceRadialCoordinates y) := by
    have hf : DifferentiableAt ℝ (fun x => entranceStableRadius x / entranceClockRate x) (Ψ (entranceRadialCoordinates y)) := by
      rw [H.apply_base]
      exact hr.mul ((hasFDerivAt_inv hD0).differentiableAt.comp y hD)
    exact hf.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have hright : DifferentiableAt ℝ
      (fun z => entranceStrongRemainder (Ψ z) / (entranceStableRadius (Ψ z) * entranceClockRate (Ψ z)))
      (entranceRadialCoordinates y) := by
    have hf : DifferentiableAt ℝ
        (fun x => entranceStrongRemainder x / (entranceStableRadius x * entranceClockRate x)) (Ψ (entranceRadialCoordinates y)) := by
      rw [H.apply_base]
      exact hE.mul ((hasFDerivAt_inv (mul_ne_zero hr0 hD0)).differentiableAt.comp y (hr.mul hD))
    exact hf.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have heq : (fun z => entranceRadialStrongCoefficient (Ψ z)) =
      (fun z => -(entranceStableRadius (Ψ z) / entranceClockRate (Ψ z)) +
        entranceStrongRemainder (Ψ z) / (entranceStableRadius (Ψ z) * entranceClockRate (Ψ z))) := by
    funext z
    simpa only [neg_div] using entranceRadialStrongCoefficient_split (Ψ z)
  have hsum := hleft.hasFDerivAt.neg.add hright.hasFDerivAt
  change HasFDerivAt (fun z => -(entranceStableRadius (Ψ z) / entranceClockRate (Ψ z)) +
    entranceStrongRemainder (Ψ z) / (entranceStableRadius (Ψ z) * entranceClockRate (Ψ z))) _ (entranceRadialCoordinates y) at hsum
  dsimp only
  rw [heq, hsum.fderiv]
  simp only [add_apply, neg_apply]
  rw [H.clock_quotient_differential hr hD0 v, H.radius_differential v,
    H.radial_quotient_differential hE hr0 hD0 v]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.EntranceRadialInverseAt.clock_radial_remainder {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hchi : entranceStablePhase y - 1 ≠ 0) (hPM : entranceStablePartial y 0 ≠ 0) :
    entranceStableRadius y *
        fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) (Pi.single 0 1) - entranceClockRate y =
      entranceStrongBracket y / entranceStablePartial y 0 +
        y 2 ^ 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) + coupling (y 1) (y 2) (y 3) := by
  rw [H.clock_radial_cancellation, entranceStableRadius_sq]
  unfold entranceStrongBracket
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_entranceClock_radial_cancellation_bound :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        |entranceStableRadius y *
            fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) (Pi.single 0 1) - entranceClockRate y| ≤
          C * (y 2 ^ 2 / k + y 1 * y 2 + (y 1 + y 3) ^ 2) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceStrongRemainder_bounds
  refine ⟨2 * C + 5, by positivity, ?_⟩
  intro k y hk hy Ψ H
  let b := y 1 + y 3
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hU := hy.2.2.1.1
  have hV := hy.2.2.2.1.1
  have hW := hy.2.2.2.2.1
  have hb : 0 ≤ b := add_nonneg hU hW
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hchi0 : 0 < entranceStablePhase y - 1 := by linarith [hchi.1]
  have hPM0 : 0 < entranceStablePartial y 0 := by linarith [hPM.1]
  have hden : k / 4 ≤ (entranceStablePhase y - 1) * entranceStablePartial y 0 := by
    have Hprod := mul_le_mul hchi.1 hPM.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hchi0.le
    nlinarith only [Hprod]
  have hF : |entranceStrongBracket y / entranceStablePartial y 0| ≤ 2 * C * b ^ 2 := by
    rw [abs_div, abs_of_pos hPM0]
    calc
      _ ≤ (C * b ^ 2 / k) / (1 / 2) := div_le_div₀ (by positivity) (HC k y hk hy).1 (by norm_num) hPM.1
      _ = 2 * C * b ^ 2 / k := by ring
      _ ≤ _ := div_le_self (by positivity) hk1
  have hterm : |y 2 ^ 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0)| ≤ 4 * (y 2 ^ 2 / k) := by
    rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (mul_pos hchi0 hPM0)]
    calc
      _ ≤ y 2 ^ 2 / (k / 4) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
      _ = _ := by ring
  have hc : |coupling (y 1) (y 2) (y 3)| ≤ y 1 * y 2 + b ^ 2 := by
    have hdiff : |y 3 - y 1| ≤ b := by
      calc
        _ ≤ |y 3| + |y 1| := abs_sub _ _
        _ = b := by rw [abs_of_nonneg hW, abs_of_nonneg hU]; dsimp [b]; ring
    have heq : coupling (y 1) (y 2) (y 3) = y 1 * y 2 + y 1 * (y 3 - y 1) := by unfold coupling; ring
    rw [heq]
    calc
      _ ≤ |y 1 * y 2| + |y 1 * (y 3 - y 1)| := abs_add_le _ _
      _ = y 1 * y 2 + y 1 * |y 3 - y 1| := by rw [abs_of_nonneg (mul_nonneg hU hV), abs_mul, abs_of_nonneg hU]
      _ ≤ y 1 * y 2 + b * b := add_le_add le_rfl
        (mul_le_mul (by dsimp [b]; linarith only [hW]) hdiff (abs_nonneg _) hb)
      _ = _ := by ring
  rw [H.clock_radial_remainder hchi0.ne' hPM0.ne']
  calc
    _ ≤ |entranceStrongBracket y / entranceStablePartial y 0| +
        |y 2 ^ 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0)| + |coupling (y 1) (y 2) (y 3)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * C * b ^ 2 + 4 * (y 2 ^ 2 / k) + (y 1 * y 2 + b ^ 2) := add_le_add (add_le_add hF hterm) hc
    _ ≤ _ := by
      have hx : 0 ≤ y 2 ^ 2 / k := by positivity
      have hz : 0 ≤ y 1 * y 2 := mul_nonneg hU hV
      change _ ≤ (2 * C + 5) * (y 2 ^ 2 / k + y 1 * y 2 + b ^ 2)
      nlinarith only [hC, hx, hz, sq_nonneg b, mul_nonneg hC.le hx, mul_nonneg hC.le hz]

end
end


set_option maxHeartbeats 600000 in
/-- The strong coefficient has the improved radial decay in (C.21). -/
theorem solution :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let z := entranceRadialCoordinates y
        |entranceRadialStrongCoefficient y| ≤ C ∧
        |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 0 1)| ≤ C / k ^ 2 ∧
        |fderiv ℝ (fun z => entranceStrongRemainder (Ψ z)) z (Pi.single 0 1)| ≤
          C * (y 2 * (y 1 + y 3) + (y 1 + y 3) ^ 2) / k := by
  obtain ⟨C, hC, HC⟩ := exists_entranceStrongRemainder_bounds
  obtain ⟨K, hK, HK⟩ := exists_entranceClock_radial_cancellation_bound
  obtain ⟨J, _, HJ⟩ := exists_entranceRadialInverse_column_bounds
  refine ⟨256 * (C + K + 1), by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  let b := y 1 + y 3
  let s := y 2 * b + b ^ 2
  let z := entranceRadialCoordinates y
  let Q := fderiv ℝ (fun z => entranceClockRate (Ψ z)) z
  let E := fderiv ℝ (fun z => entranceStrongRemainder (Ψ z)) z
  have hU := hy.2.2.1.1
  have hV := hy.2.2.2.1.1
  have hW := hy.2.2.2.2.1
  have hb : 0 ≤ b := add_nonneg hU hW
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s ≤ 2 := by
    have Hprod := mul_le_mul hy.2.2.2.1.2 hb1 hb (by norm_num : (0 : ℝ) ≤ 1)
    dsimp [s]; nlinarith only [Hprod, hb2]
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hU]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hW]; linarith [hy.2.2.2.2.2]
  obtain ⟨_, hE, hEM⟩ := HC k y hk hy
  have hMr := (HJ k y hk hy hv Ψ H).1
  rw [H.phase_partials.1] at hMr
  have hEr : |E (Pi.single 0 1)| ≤ 8 * C * s / k := by
    dsimp only [E, z]
    rw [(H.scalar_partials ((contDiffAt_entranceStrongRemainder_one hm hu hw).differentiableAt (by norm_num))).1,
      abs_mul, abs_of_nonneg (by linarith only [hMr.1])]
    calc
      _ ≤ 8 * (C * s / k) := mul_le_mul hMr.2 hEM (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hEcoarse : |entranceStrongRemainder y| ≤ 2 * C :=
    hE.trans (by nlinarith only [mul_le_mul_of_nonneg_left hs2 hC.le])
  have hErcoarse : |E (Pi.single 0 1)| ≤ 16 * C / k := hEr.trans
    (div_le_div_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_left hs2 hC.le]) hk0.le)
  obtain ⟨_, hr, _⟩ := entranceRegion_stable_radial_bounds hk hy
  have hD := entranceRegion_speed hk hy
  have hr0 := entranceStableRadius_pos hv
  have hD0 := entranceRegion_clock_pos hk hy
  have hDlo : k / 2 ≤ entranceClockRate y := by linarith only [hD.1, hk0]
  have hden : k ^ 2 / 4 ≤ entranceStableRadius y * entranceClockRate y := by
    have Hprod := mul_le_mul hr.1 hDlo (by positivity) hr0.le
    nlinarith only [Hprod]
  have hDsq : k ^ 2 / 4 ≤ entranceClockRate y ^ 2 := by
    have Hpow := pow_le_pow_left₀ (show 0 ≤ k / 2 by positivity) hDlo 2
    nlinarith only [Hpow]
  have hQ : |Q (Pi.single 0 1)| ≤ 8 := by
    dsimp only [Q, z]
    rw [H.clock_partials.1, abs_of_nonneg (by linarith only [hMr.1])]
    exact hMr.2
  have hcancel : |entranceStableRadius y * Q (Pi.single 0 1) - entranceClockRate y| ≤ 3 * K := by
    have hv2 : y 2 ^ 2 ≤ 1 := by nlinarith only [hV, hy.2.2.2.1.2]
    have hvterm : y 2 ^ 2 / k ≤ 1 := (div_le_self (sq_nonneg _) hk1).trans hv2
    have huv : y 1 * y 2 ≤ 1 := by
      have Hprod := mul_le_mul (show y 1 ≤ 1 by linarith [hy.2.2.1.2]) hy.2.2.2.1.2 hV (by norm_num : (0 : ℝ) ≤ 1)
      simpa using Hprod
    exact (HK k y hk hy Ψ H).trans (by
      have HB := mul_le_mul_of_nonneg_left (show y 2 ^ 2 / k + y 1 * y 2 + b ^ 2 ≤ 3 by linarith only [hvterm, huv, hb2]) hK.le
      nlinarith only [HB])
  have hquot : |entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y)| ≤ 8 * C / k ^ 2 := by
    rw [abs_div, abs_of_pos (mul_pos hr0 hD0)]
    calc
      _ ≤ (2 * C) / (k ^ 2 / 4) := div_le_div₀ (by positivity) hEcoarse (by positivity) hden
      _ = _ := by ring
  have hvalue : |entranceRadialStrongCoefficient y| ≤ 4 + 8 * C := by
    rw [entranceRadialStrongCoefficient_split]
    calc
      _ ≤ |(-entranceStableRadius y) / entranceClockRate y| +
          |entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y)| := abs_add_le _ _
      _ = entranceStableRadius y / entranceClockRate y +
          |entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y)| := by
        rw [abs_div, abs_neg, abs_of_pos hr0, abs_of_pos hD0]
      _ ≤ (2 * k) / (k / 2) + 8 * C / k ^ 2 := add_le_add (div_le_div₀ (by positivity) hr.2 (by positivity) hDlo) hquot
      _ = 4 + 8 * C / k ^ 2 := by field_simp; ring
      _ ≤ _ := add_le_add le_rfl (div_le_self (by positivity) (one_le_pow₀ hk1))
  have hlog : |1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y| ≤ 18 / k := by
    calc
      _ ≤ 1 / entranceStableRadius y + |Q (Pi.single 0 1)| / entranceClockRate y := by
        simpa only [abs_div, abs_one, abs_of_pos hr0, abs_of_pos hD0] using
          abs_add_le (1 / entranceStableRadius y) (Q (Pi.single 0 1) / entranceClockRate y)
      _ ≤ 1 / (k / 2) + 8 / (k / 2) := add_le_add
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) hr.1)
        (div_le_div₀ (by norm_num) hQ (by positivity) hDlo)
      _ = _ := by ring
  have hderiv : |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 0 1)| ≤
      (12 * K + 208 * C) / k ^ 2 := by
    rw [H.strong_differential hk hy hv]
    change |(entranceStableRadius y * Q (Pi.single 0 1) - entranceClockRate y * 1) / entranceClockRate y ^ 2 +
      E (Pi.single 0 1) / (entranceStableRadius y * entranceClockRate y) -
      entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) *
        (1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y)| ≤ _
    rw [mul_one]
    calc
      _ ≤ |entranceStableRadius y * Q (Pi.single 0 1) - entranceClockRate y| / entranceClockRate y ^ 2 +
          |E (Pi.single 0 1)| / (entranceStableRadius y * entranceClockRate y) +
          |entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y)| *
            |1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y| := by
        have Htri (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        have ht := Htri ((entranceStableRadius y * Q (Pi.single 0 1) - entranceClockRate y) / entranceClockRate y ^ 2)
            (E (Pi.single 0 1) / (entranceStableRadius y * entranceClockRate y))
            (entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) *
              (1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y))
        rw [abs_div (entranceStableRadius y * Q (Pi.single 0 1) - entranceClockRate y) (entranceClockRate y ^ 2),
          abs_of_nonneg (sq_nonneg (entranceClockRate y))] at ht
        simpa only [abs_div, abs_of_pos (mul_pos hr0 hD0), abs_mul] using ht
      _ ≤ (3 * K) / (k ^ 2 / 4) + (16 * C / k) / (k ^ 2 / 4) + (8 * C / k ^ 2) * (18 / k) :=
        add_le_add (add_le_add (div_le_div₀ (by positivity) hcancel (by positivity) hDsq)
          (div_le_div₀ (by positivity) hErcoarse (by positivity) hden))
          (mul_le_mul hquot hlog (abs_nonneg _) (by positivity))
      _ = 12 * K / k ^ 2 + 208 * C / k ^ 3 := by ring
      _ ≤ 12 * K / k ^ 2 + 208 * C / k ^ 2 := add_le_add le_rfl
        (div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hk1 (by norm_num : 2 ≤ 3)))
      _ = _ := by ring
  dsimp only
  refine ⟨hvalue.trans (by linarith only [hC, hK]), hderiv.trans ?_, hEr.trans ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith only [hC, hK]) (sq_nonneg k)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith only [hC, hK] : 8 * C ≤ 256 * (C + K + 1)) hs) hk0.le
