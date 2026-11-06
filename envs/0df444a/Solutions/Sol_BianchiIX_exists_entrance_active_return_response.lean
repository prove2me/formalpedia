-- Prove2me | solution 1 for BianchiIX.exists_entrance_active_return_response
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:27:41.853562+00:00
-- url     : https://prove2.me/submissions/afad7e02-3788-4e87-8cbe-4762e2d9ee9d

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
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_FlowComposition
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Theorems.Thm_BianchiIX_abs_le_affine_exp_of_clock_damping
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_projectiveOriginalField
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuousOn_normalizedProjectiveRate
import Theorems.Thm_BianchiIX_entranceReturn_region
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entranceReturn_walls_pos
import Theorems.Thm_BianchiIX_entrance_denom_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_entrance_transport_initial_weights
import Theorems.Thm_BianchiIX_exists_entranceRadialDrift_basic_bounds
import Theorems.Thm_BianchiIX_exists_entrance_ordinary_return_response
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_coordinate_variation
import Theorems.Thm_BianchiIX_hasDerivAt_fromProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_hasFDerivAt_stableBoundaryProjection_in_band
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_integral_le_of_exp_decay
import Theorems.Thm_BianchiIX_mem_normalizedMaxDomain_retime
import Theorems.Thm_BianchiIX_norm_le_exp_of_signedRowSum
import Theorems.Thm_BianchiIX_normalizedFlowDifferential_field
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
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.mul_neg_log_le_one {w : ℝ} (hw : 0 < w) : w * (-Real.log w) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hw) hw.le
  have hid : w * (1 - w⁻¹) = w - 1 := by field_simp
  rw [hid] at H
  nlinarith only [H, hw]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_phase_waiting_budget {u v w θ : ℝ}
    (hu : 0 ≤ u) (hv : 0 < v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    0 ≤ u * v + θ * (v * w) ^ 2 ∧
      u * v + θ * (v * w) ^ 2 ≤ u + w ∧
      (-Real.log v) * (u * v + θ * (v * w) ^ 2) ≤ u + w := by
  have hv0 := hv.1.le
  have hw0 := hw.1
  have hθ0 := hθ.1
  have hW2 : w ^ 2 ≤ w := by nlinarith only [mul_le_mul_of_nonneg_left hw.2 hw.1]
  have htail : θ * v * w ^ 2 ≤ w :=
    ((mul_le_of_le_one_left (sq_nonneg w)
      ((mul_le_of_le_one_left hv0 hθ.2).trans hv.2)).trans hW2)
  have hP : 0 ≤ u + θ * v * w ^ 2 := by positivity
  have hPbound : u + θ * v * w ^ 2 ≤ u + w := add_le_add le_rfl htail
  have hLv : (-Real.log v) * v ≤ 1 := by simpa only [mul_comm] using mul_neg_log_le_one hv.1
  refine ⟨by positivity, ?_, ?_⟩
  · calc
      _ = v * (u + θ * v * w ^ 2) := by ring
      _ ≤ u + θ * v * w ^ 2 := mul_le_of_le_one_left hP hv.2
      _ ≤ _ := hPbound
  · calc
      _ = ((-Real.log v) * v) * (u + θ * v * w ^ 2) := by ring
      _ ≤ u + θ * v * w ^ 2 := mul_le_of_le_one_left hP hLv
      _ ≤ _ := hPbound

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

private theorem BianchiIX.entrance_active_phase_response {A F K H J G Q k : ℝ}
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hH : 0 ≤ H ∧ H ≤ 2) (hk : 1 ≤ k)
    (hJ : J / k ≤ 21 * H) (hG : |G| ≤ A * H)
    (hresponse : |Q - G| ≤ 2 * (K * J / k) + 2 * (F * H / k ^ 2) * |G|) :
    |Q| ≤ (A * (1 + 4 * F) + 42 * K) * H := by
  have hsource : K * J / k ≤ 21 * K * H := by
    simpa only [mul_div_assoc, mul_assoc, mul_left_comm K 21] using mul_le_mul_of_nonneg_left hJ hK
  have hphase : F * H / k ^ 2 ≤ 2 * F := by
    calc
      _ ≤ F * H := div_le_self (mul_nonneg hF hH.1) (one_le_pow₀ hk)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hH.2 hF]
  have hinc : |Q - G| ≤ 42 * K * H + 4 * F * |G| := by
    nlinarith only [hresponse, hsource, mul_le_mul_of_nonneg_right hphase (abs_nonneg G)]
  have htriangle : |Q| ≤ |Q - G| + |G| := by simpa using abs_add_le (Q - G) G
  have HG := mul_le_mul_of_nonneg_left hG (show 0 ≤ 1 + 4 * F by positivity)
  nlinarith only [hinc, htriangle, HG]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_active_wall_response {T A K H J G R A₀ k u w l : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hk : 0 ≤ k) (hu : 0 ≤ u) (hw : 0 ≤ w) (hl : 0 ≤ l)
    (hinitial : A₀ ≤ 12 * k * u + 9 * w) (hJ : J / k ≤ 21 * H) (hG : |G| ≤ A * H)
    (hresponse : R ≤ T * (A₀ + 2 * l * (|G| + K * J / k))) :
    R ≤ T * (21 + 2 * (A + 21 * K)) * (k * u + w + l * H) := by
  have hsource : K * J / k ≤ 21 * K * H := by
    simpa only [mul_div_assoc, mul_assoc, mul_left_comm K 21] using mul_le_mul_of_nonneg_left hJ hK
  have HG : |G| + K * J / k ≤ (A + 21 * K) * H :=
    (add_le_add hG hsource).trans_eq (by ring)
  have Hscaled := mul_le_mul_of_nonneg_left HG (show 0 ≤ 2 * l by positivity)
  have HC : A₀ + 2 * l * (|G| + K * J / k) ≤
      (21 + 2 * (A + 21 * K)) * (k * u + w + l * H) := by
    have hnonneg : 0 ≤ 2 * (A + 21 * K) * (k * u + w) := by positivity
    nlinarith only [hinitial, Hscaled, hnonneg, mul_nonneg hk hu, hw, mul_nonneg hl hH]
  exact hresponse.trans ((mul_le_mul_of_nonneg_left HC hT).trans_eq (by ring))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entrance_active_log_columns {C k u v w l H p q βU βW : ℝ}
    (hC : 0 ≤ C) (hk : 1 ≤ k) (hu : u ≤ 1) (hv : 0 < v) (hw : w ≤ 1)
    (hLH : l * H ≤ 2) (hU : |βU| ≤ 12 * k) (hW : |βW| ≤ 9)
    (herror : |v * p + βU| + k ^ 2 * |v * q + βW| ≤ C * (k * u + w + l * H)) :
    |p| ≤ (12 + 4 * C) * k / v ∧ |q| ≤ (12 + 4 * C) / v := by
  have hk0 : 0 < k := by linarith
  have hsum : k * u + w + l * H ≤ 4 * k := by
    nlinarith only [mul_le_mul_of_nonneg_left hu hk0.le, hw, hLH, hk]
  have HE : |v * p + βU| + k ^ 2 * |v * q + βW| ≤ 4 * C * k :=
    herror.trans ((mul_le_mul_of_nonneg_left hsum hC).trans_eq (by ring))
  have hstrong : |v * p| ≤ |v * p + βU| + |βU| := by
    simpa using abs_sub (v * p + βU) βU
  have hweak : |v * q| ≤ |v * q + βW| + |βW| := by
    simpa using abs_sub (v * q + βW) βW
  have hwerr : |v * q + βW| ≤ 4 * C := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hk0)).mp
    have hkk : k ≤ k ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hk hk0.le]
    have HC := mul_le_mul_of_nonneg_left hkk (show 0 ≤ 4 * C by positivity)
    nlinarith only [HE, HC, abs_nonneg (v * p + βU)]
  constructor
  · apply (le_div_iff₀ hv).mpr
    rw [abs_mul, abs_of_pos hv] at hstrong
    nlinarith only [hstrong, hU, HE, mul_nonneg (sq_nonneg k) (abs_nonneg (v * q + βW))]
  · apply (le_div_iff₀ hv).mpr
    rw [abs_mul, abs_of_pos hv] at hweak
    nlinarith only [hweak, hwerr, hW]

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
open Set

private theorem BianchiIX.fromProjectiveState_fderiv_field {y : ProjectiveState} (hD : projectiveStateDenom y ≠ 0) :
    fderiv ℝ fromProjectiveState y (projectiveField y) =
      (projectiveStateDenom y / 6) • normalizedField (fromProjectiveState y) := by
  let β : ℝ → ProjectiveState := fun t => y + t • projectiveField y
  have hbase : β 0 = y := by simp [β]
  have hβ : HasDerivAt β (projectiveField y) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (projectiveField y)) using 1
    simp
  have hd := ((contDiffAt_fromProjectiveState 1 hD).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hbase.symm ▸ hd).comp_hasDerivAt 0 hβ
  have H' := hasDerivAt_fromProjectiveState
    (show HasDerivAt β (projectiveField (β 0)) 0 by simpa only [hbase] using hβ)
    (by simpa only [hbase] using hD)
  simpa only [hbase] using H.unique H'

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

private theorem BianchiIX.entranceLogField_active {y : ProjectiveState} (hD : entranceClockRate y ≠ 0) :
    entranceLogField y 2 = y 2 := by
  change (entranceClockRate y)⁻¹ * (entranceClockRate y * y 2) = y 2
  rw [← mul_assoc, inv_mul_cancel₀ hD, one_mul]

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
open Set Filter
open scoped Topology

private theorem BianchiIX.entrance_initial_denom_pos {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) : 0 < projectiveStateDenom y := by
  have hr : |coreRadius (y 0) (y 2) - coreRadius (y 0) (y 2)| ≤ coreRadius (y 0) (y 2) / 100 := by
    rw [sub_self, abs_zero]
    linarith
  exact (entrance_denom_bounds hk (entrance_phase_bounds hk hm hr ⟨hv.1.le, hv.2.le⟩)
    hu ⟨hv.1.le, hv.2.le⟩ hw).1

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

private theorem BianchiIX.entranceWallLogRates_base_bounds {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    |1 + coupling (y 1) (y 2) (y 3)| ≤ 2 ∧
      |entranceStrongLogRate y| ≤ 12 * k ∧ |entranceWeakLogRate y| ≤ 9 := by
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 ≤ y 0 := by linarith [hy.1]
  have hm : y 0 ≤ 3 * k := by linarith [(entranceRegion_phase hk hy).2]
  have hu0 := hy.2.2.1.1
  have hu1 : y 1 ≤ 1 := by linarith [hy.2.2.1.2]
  have hw1 : y 3 ≤ 1 := by linarith [hy.2.2.2.2.2]
  have huv : |y 2 - y 3| ≤ 1 := abs_le.mpr ⟨by linarith [hy.2.2.2.1.1],
    by linarith [hy.2.2.2.1.2, hy.2.2.2.2.1]⟩
  have hu2 : y 1 ^ 2 ≤ 1 := by nlinarith [pow_le_pow_left₀ hu0 hu1 2]
  have hC := connection_coupling_bounds hu0 hy.2.2.2.1 ⟨hy.2.2.2.2.1, hw1⟩
  have hc : |1 + coupling (y 1) (y 2) (y 3)| ≤ 2 :=
    abs_le.mpr ⟨by linarith [hC.1], by linarith [hC.2, hy.2.2.1.2]⟩
  have hD := entranceRegion_clock_pos hk hy
  have hDlo : k / 2 ≤ entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]
  refine ⟨hc, ?_, ?_⟩
  · have hm2 : y 0 ^ 2 ≤ 9 * k ^ 2 := by nlinarith [pow_le_pow_left₀ hm0 hm 2]
    have hdiff2 : (y 2 - y 3) ^ 2 ≤ 1 := by nlinarith [sq_abs (y 2 - y 3), pow_le_pow_left₀ (abs_nonneg _) huv 2]
    have hr : |connectionStrongRate (y 0) (y 1) (y 2) (y 3)| ≤ 6 * k ^ 2 := by
      unfold connectionStrongRate
      apply abs_le.mpr
      constructor <;> nlinarith only [hm2, hdiff2, hu2, sq_nonneg (y 0), sq_nonneg (y 2 - y 3), sq_nonneg (y 1), hk1, hk0]
    change |connectionStrongRate (y 0) (y 1) (y 2) (y 3) / entranceClockRate y| ≤ _
    rw [abs_div, abs_of_pos hD]
    exact (div_le_iff₀ hD).mpr (hr.trans (by nlinarith only [hDlo, hk0]))
  · change |-1 - 2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y| ≤ _
    have hq : |2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y| ≤ 8 := by
      rw [abs_div, abs_mul, abs_of_pos hD, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply (div_le_iff₀ hD).mpr
      nlinarith only [hc, hDlo, hk1]
    exact (abs_sub _ _).trans (by norm_num only [abs_neg, abs_one]; linarith only [hq])

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

private theorem BianchiIX.exists_entrance_transport_drift_bound :
    ∃ A > (0 : ℝ), ∀ (k θ : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      (θ = 1 ∨ θ = 1 / k ^ 2) →
      |entranceRadialDrift y| ≤ A * (y 1 * y 2 + θ * (y 2 * y 3) ^ 2) := by
  obtain ⟨A, hA, HA⟩ := exists_entranceRadialDrift_basic_bounds
  refine ⟨A, hA, ?_⟩
  intro k θ y hk hy hv hθ
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk hy hv
  have H := (HA k y hk hy hv Ψ HΨ).1
  rcases hθ with rfl | rfl
  · apply H.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hA.le)
    have hk1 : 1 ≤ k := by linarith
    calc
      _ ≤ y 2 ^ 2 * y 3 ^ 2 := div_le_self (by positivity) (one_le_pow₀ hk1)
      _ = _ := by ring
  · convert! H using 1
    ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.hasFDerivAt_entranceLogWalls {y : ProjectiveState} (k : ℝ)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) :
    HasFDerivAt (entranceLogWalls k)
      (ContinuousLinearMap.pi (![(y 1)⁻¹ • ContinuousLinearMap.proj 1,
        k ^ 2 • ((y 3)⁻¹ • ContinuousLinearMap.proj 3)] : Fin 2 → (ProjectiveState →L[ℝ] ℝ))) y := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y).log hu
  · exact ((hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y).log hw).const_mul (k ^ 2)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.entranceLogWalls_fderiv_apply {y : ProjectiveState} (k : ℝ)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) (v : ProjectiveState) :
    fderiv ℝ (entranceLogWalls k) y v = entranceWallTangent k y v := by
  rw [(hasFDerivAt_entranceLogWalls k hu hw).fderiv]
  ext i
  fin_cases i <;> simp [entranceWallTangent, div_eq_mul_inv, mul_comm]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRegion_radialDifferential_inverse {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    Function.LeftInverse (entranceRadialInverseDifferential y) (entranceRadialDifferential y) ∧
      Function.RightInverse (entranceRadialInverseDifferential y) (entranceRadialDifferential y) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  exact entranceRadialDifferential_inverse hm hu hw hv (by linarith [hchi.1]) (by linarith [hPM.1])

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.EntranceRadialInverseAt.hasFDerivAt_return {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    HasFDerivAt (fun z => entranceReturnState (Ψ z))
      ((fderiv ℝ entranceReturnState y).comp (entranceRadialInverseDifferential y)) (entranceRadialCoordinates y) := by
  have hd : HasFDerivAt entranceReturnState (fderiv ℝ entranceReturnState y) (Ψ (entranceRadialCoordinates y)) := by
    rw [HΨ.apply_base]
    exact ((entranceReturn_regular hk hm hu hv hw).2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  simpa only [Function.comp_def] using hd.comp (entranceRadialCoordinates y) HΨ.hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalizedEventDifferential_field {g : NormalizedState → ℝ} {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) (hr : normalizedEventRate g x t₀ t ≠ 0) :
    normalizedEventDifferential g x t₀ t (normalizedField x) = 0 := by
  simp only [normalizedEventDifferential, normalizedEventTimeDifferential, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, ContinuousLinearMap.comp_apply,
    normalizedFlowDifferential_field ht]
  change normalizedField (normalizedMaxCurve x t₀ t) +
    (-(normalizedEventRate g x t₀ t)⁻¹ * normalizedEventRate g x t₀ t) •
      normalizedField (normalizedMaxCurve x t₀ t) = 0
  simp [hr]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceReturnState_fderiv_field {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    fderiv ℝ entranceReturnState y (projectiveField y) = 0 ∧
      fderiv ℝ entranceReturnState y (entranceLogField y) = 0 := by
  have HR := entranceReturn_regular hk hm hu hv hw
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HR.1.1.1.1.le, le_rfl⟩
  have hd := entrance_initial_denom_pos hk hm hu hv hw
  have hzero : fderiv ℝ entranceReturnState y (projectiveField y) = 0 := by
    rw [HR.2.2.2.2.1.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      fromProjectiveState_fderiv_field hd.ne', map_smul,
      normalizedEventDifferential_field (HR.1.2.1 _ ht).1 (HR.1.2.2.2 _ ht).ne', smul_zero, map_zero]
  refine ⟨hzero, ?_⟩
  rw [entranceLogField, map_smul, hzero, smul_zero]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceRadialDifferential_logField {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    entranceRadialDifferential y (entranceLogField y) =
      ![entranceRadialDrift y, y 1 * entranceStrongLogRate y, y 2, y 3 * entranceWeakLogRate y] := by
  have hD := (entranceRegion_clock_pos hk hy).ne'
  have HE : fderiv ℝ entranceStableRadius y (entranceLogField y) = entranceRadialDrift y :=
    (entranceRadialDrift_lie_eventuallyEq hk hy hv).self_of_nhds
  obtain ⟨hU, hW⟩ := entranceWallLogRates_field hD
  rw [entranceRadialDifferential_apply, HE, entranceLogField_active hD]
  ext i
  fin_cases i
  · rfl
  · change (entranceClockRate y)⁻¹ * projectiveField y 1 = y 1 * entranceStrongLogRate y
    rw [hU]
    field_simp
  · rfl
  · change (entranceClockRate y)⁻¹ * projectiveField y 3 = y 3 * entranceWeakLogRate y
    rw [hW]
    field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.EntranceRadialInverseAt.return_active_direction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000)
    {p : ProjectiveState → E} (hp : DifferentiableAt ℝ p (entranceReturnState y)) :
    let D := fderiv ℝ (fun z => p (entranceReturnState (Ψ z))) (entranceRadialCoordinates y)
    y 2 • D (Pi.single 2 1) =
      -D ![entranceRadialDrift y, y 1 * entranceStrongLogRate y, 0, y 3 * entranceWeakLogRate y] := by
  intro D
  have hy : entranceRegion (coreRadius (y 0) (y 2)) y :=
    ⟨hm, by rw [sub_self, abs_zero]; linarith, hu, ⟨hv.1.le, hv.2.le⟩, hw⟩
  have hp' : HasFDerivAt p (fderiv ℝ p (entranceReturnState y))
      (entranceReturnState (Ψ (entranceRadialCoordinates y))) := by
    rw [HΨ.apply_base]
    exact hp.hasFDerivAt
  have HD := hp'.comp (entranceRadialCoordinates y) (HΨ.hasFDerivAt_return hk hm hu hv hw)
  simp only [Function.comp_def] at HD
  have Hzero : D (entranceRadialDifferential y (entranceLogField y)) = 0 := by
    dsimp [D]
    rw [HD.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      (entranceRegion_radialDifferential_inverse hk hy hv.1).1,
      (entranceReturnState_fderiv_field hk hm hu hv hw).2, map_zero]
  have heq : entranceRadialDifferential y (entranceLogField y) =
      ![entranceRadialDrift y, y 1 * entranceStrongLogRate y, 0, y 3 * entranceWeakLogRate y] +
        y 2 • Pi.single 2 1 := by
    rw [entranceRadialDifferential_logField hk hy hv.1]
    ext i
    fin_cases i <;> simp
  rw [heq, map_add, map_smul] at Hzero
  exact eq_neg_of_add_eq_zero_right Hzero

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceLogWalls_comp_fderiv_scale {g : ProjectiveState → ProjectiveState} {z : ProjectiveState}
    (hg : DifferentiableAt ℝ g z) (hu : g z 1 ≠ 0) (hw : g z 3 ≠ 0) (k : ℝ) (d : ProjectiveState) :
    fderiv ℝ (fun q => entranceLogWalls k (g q)) z d =
      ![fderiv ℝ (fun q => entranceLogWalls 1 (g q)) z d 0,
        k ^ 2 * fderiv ℝ (fun q => entranceLogWalls 1 (g q)) z d 1] := by
  have HE (a : ℝ) : fderiv ℝ (fun q => entranceLogWalls a (g q)) z d =
      entranceWallTangent a (g z) (fderiv ℝ g z d) := by
    have H := (hasFDerivAt_entranceLogWalls a hu hw).differentiableAt.hasFDerivAt.comp z hg.hasFDerivAt
    simp only [Function.comp_def] at H
    rw [H.fderiv, ContinuousLinearMap.comp_apply, entranceLogWalls_fderiv_apply a hu hw]
  rw [HE k, HE 1]
  ext i
  fin_cases i <;> simp [entranceWallTangent]

end
end


/-- The active-wall column of the actual return, recovered without integrating a fourth variational equation. -/
theorem solution :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∀ (Ψ : ProjectiveState → ProjectiveState), EntranceRadialInverseAt y Ψ →
      let z := entranceRadialCoordinates y
      let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
      let L := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
      let H := y 1 * y 2 + θ * (y 2 * y 3) ^ 2
      |fderiv ℝ Q z (Pi.single 2 1)| ≤ C * (y 1 + θ * y 2 * (y 3) ^ 2) ∧
      |y 2 * fderiv ℝ L z (Pi.single 2 1) 0 + entranceStrongLogRate y| +
        k ^ 2 * |y 2 * fderiv ℝ L z (Pi.single 2 1) 1 + entranceWeakLogRate y| ≤
          C * (k * y 1 + y 3 + (-Real.log (y 2)) * H) ∧
      |fderiv ℝ L z (Pi.single 2 1) 0| ≤ C * k / y 2 ∧
      |fderiv ℝ L z (Pi.single 2 1) 1| ≤ C / y 2 := by
  obtain ⟨T, hT, K, hK, F, hF, ε, hε, hεsmall, HP⟩ := exists_entrance_ordinary_return_response
  obtain ⟨A, hA, HA⟩ := exists_entrance_transport_drift_bound
  let P := A * (1 + 4 * F) + 42 * K
  let B := T * (21 + 2 * (A + 21 * K))
  let C := P + 12 + 5 * B
  have hP : 0 < P := by dsimp [P]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCP : P ≤ C := by dsimp [C]; linarith only [hB]
  have hCB : B ≤ C := by dsimp [C]; linarith only [hP, hB]
  have hClog : 12 + 4 * B ≤ C := by dsimp [C]; linarith only [hP, hB]
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y θ k hk hm hu hv hw hθ Ψ HΨ z Q L H
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have hu1 : y 1 ≤ 1 := by linarith [hu'.2]
  have hw1 : y 3 ≤ 1 := by linarith [hw'.2]
  have hy : entranceRegion k y := ⟨hm, by rw [sub_self, abs_zero]; dsimp [k]; linarith,
    hu', ⟨hv.1.le, hv.2.le⟩, hw'⟩
  have hθ01 : 0 ≤ θ ∧ θ ≤ 1 := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · exact ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hH := entrance_phase_waiting_budget hu.1.le ⟨hv.1, hv.2.le⟩ ⟨hw.1.le, hw1⟩ hθ01
  have hH2 : H ≤ 2 := by linarith only [hH.2.1, hu1, hw1]
  have hLH : (-Real.log (y 2)) * H ≤ 2 := by linarith only [hH.2.2, hu1, hw1]
  have hlog : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hG : |entranceRadialDrift y| ≤ A * H := HA k θ y hk hy hv.1 (hθ.imp_right And.left)
  obtain ⟨_, hU, hW⟩ := entranceWallLogRates_base_bounds hk hy
  let d : ProjectiveState := ![entranceRadialDrift y, y 1 * entranceStrongLogRate y, 0, y 3 * entranceWeakLogRate y]
  let J := y 2 * |d 1| + (y 1 * y 2 + θ * (y 2) ^ 2 * y 3) * |d 3|
  let Dk := fderiv ℝ (fun z => entranceLogWalls k (entranceReturnState (Ψ z))) z
  have hweights := entrance_transport_initial_weights hu.1.le hv.1.le ⟨hw.1.le, hw1⟩ hθ01.1 hk1 hU hW
  have hJ : J / k ≤ 21 * H := hweights.2
  have hresponse := HP y θ hk hm hu hv hw hθ Ψ HΨ d (by simp [d])
  change |fderiv ℝ Q z d - entranceRadialDrift y| ≤
      2 * (K * J / k) + 2 * (F * H / k ^ 2) * |entranceRadialDrift y| ∧
    |Dk d 0 - d 1 / y 1| + |Dk d 1 - k ^ 2 * (d 3 / y 3)| ≤
      T * (|d 1| + |d 3| + 2 * (-Real.log (y 2)) * (|entranceRadialDrift y| + K * J / k)) at hresponse
  have HR := entranceReturn_regular hk hm hu' hv hw'
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HR.1.1.1.1.le, le_rfl⟩
  have hpos := entranceReturn_walls_pos hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩ _ ht
  have hreg : entranceRegion k (entranceReturnState y) := entranceReturn_region hk hm hu' hv hw' _ ht
  have hpQ : DifferentiableAt ℝ entranceStableRadius (entranceReturnState y) := by
    have hmR : 2 ≤ entranceReturnState y 0 := by linarith [(entranceRegion_phase hk hreg).1]
    have huR : |entranceReturnState y 1| < 1 / 200 := by
      rw [abs_of_nonneg hreg.2.2.1.1]; linarith [hreg.2.2.1.2]
    have hwR : |entranceReturnState y 3| < 1 / 200 := by
      rw [abs_of_nonneg hreg.2.2.2.2.1]; linarith [hreg.2.2.2.2.2]
    exact (contDiffAt_entranceStableRadius_two hmR huR hwR hpos.2.1).differentiableAt (by norm_num)
  have htransportQ : y 2 * fderiv ℝ Q z (Pi.single 2 1) = -fderiv ℝ Q z d :=
    HΨ.return_active_direction hk hm hu' hv hw' hpQ
  have htransportL : y 2 • Dk (Pi.single 2 1) = -Dk d :=
    HΨ.return_active_direction hk hm hu' hv hw'
      (hasFDerivAt_entranceLogWalls k hpos.1.ne' hpos.2.2.ne').differentiableAt
  have hphase : |fderiv ℝ Q z (Pi.single 2 1)| ≤ P * (y 1 + θ * y 2 * (y 3) ^ 2) := by
    have HE := entrance_active_phase_response hF.le hK.le ⟨hH.1, hH2⟩ hk1 hJ hG hresponse.1
    have HE' : |y 2 * fderiv ℝ Q z (Pi.single 2 1)| ≤ P * H := by
      rw [htransportQ, abs_neg]
      exact HE
    rw [abs_mul, abs_of_pos hv.1] at HE'
    apply (mul_le_mul_iff_left₀ hv.1).mp
    calc
      _ = y 2 * |fderiv ℝ Q z (Pi.single 2 1)| := by ring
      _ ≤ P * H := HE'
      _ = (P * (y 1 + θ * y 2 * (y 3) ^ 2)) * y 2 := by dsimp [H]; ring
  have hwalls := entrance_active_wall_response hT.le hA.le hK.le hH.1 hk0.le hu.1.le hw.1.le hlog
    hweights.1 hJ hG hresponse.2
  have hdU : d 1 / y 1 = entranceStrongLogRate y := by dsimp [d]; field_simp [hu.1.ne']
  have hdW : d 3 / y 3 = entranceWeakLogRate y := by dsimp [d]; field_simp [hw.1.ne']
  rw [hdU, hdW] at hwalls
  have hDk (i : Fin 2) : Dk d i = -(y 2 * Dk (Pi.single 2 1) i) := by
    have HE := congrFun htransportL i
    change y 2 * Dk (Pi.single 2 1) i = -Dk d i at HE
    linarith only [HE]
  have hscale : Dk (Pi.single 2 1) =
      ![fderiv ℝ L z (Pi.single 2 1) 0, k ^ 2 * fderiv ℝ L z (Pi.single 2 1) 1] := by
    apply entranceLogWalls_comp_fderiv_scale (HΨ.hasFDerivAt_return hk hm hu' hv hw').differentiableAt
    · rw [HΨ.apply_base]
      exact hpos.1.ne'
    · rw [HΨ.apply_base]
      exact hpos.2.2.ne'
  have heq : |Dk d 0 - entranceStrongLogRate y| + |Dk d 1 - k ^ 2 * entranceWeakLogRate y| =
      |y 2 * fderiv ℝ L z (Pi.single 2 1) 0 + entranceStrongLogRate y| +
        k ^ 2 * |y 2 * fderiv ℝ L z (Pi.single 2 1) 1 + entranceWeakLogRate y| := by
    rw [hDk 0, hDk 1, hscale]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show -(y 2 * fderiv ℝ L z (Pi.single 2 1) 0) - entranceStrongLogRate y =
      -(y 2 * fderiv ℝ L z (Pi.single 2 1) 0 + entranceStrongLogRate y) by ring,
      show -(y 2 * (k ^ 2 * fderiv ℝ L z (Pi.single 2 1) 1)) - k ^ 2 * entranceWeakLogRate y =
      -(k ^ 2 * (y 2 * fderiv ℝ L z (Pi.single 2 1) 1 + entranceWeakLogRate y)) by ring,
      abs_neg, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg k)]
  rw [heq] at hwalls
  have hlogs := entrance_active_log_columns hB.le hk1 hu1 hv.1 hw1 hLH hU hW hwalls
  refine ⟨hphase.trans (mul_le_mul_of_nonneg_right hCP (by positivity [hu.1, hv.1, hθ01.1])),
    hwalls.trans (mul_le_mul_of_nonneg_right hCB (by positivity [hu.1, hw.1, hH.1])),
    hlogs.1.trans ?_, hlogs.2.trans ?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hClog hk0.le) hv.1.le
  · exact div_le_div_of_nonneg_right hClog hv.1.le
