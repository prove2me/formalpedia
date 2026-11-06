-- Prove2me | solution 1 for BianchiIX.exists_restartShearReturn_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:56:01.041411+00:00
-- url     : https://prove2.me/submissions/37eb0b81-be2d-4bdb-84df-596c8ef9b602

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Definitions.Def_BianchiIX_ShearTransportData
import Theorems.Thm_BianchiIX_connectionReturn_coreExit_curve
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_exists_normalized_partialCore_return
import Theorems.Thm_BianchiIX_exists_partialCore_downward_radius_response
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_exists_restartShearPartialCore_radial_data
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_core_prefix_contraction
import Theorems.Thm_BianchiIX_normalized_core_residence
import Theorems.Thm_BianchiIX_normalized_core_return_downward
import Theorems.Thm_BianchiIX_normalized_core_return_isLeast
import Theorems.Thm_BianchiIX_normalized_partialCore_energy_band_improves
import Theorems.Thm_BianchiIX_partialCoreDownwardReturn_connection_domain
import Theorems.Thm_BianchiIX_partialCoreDownwardReturn_radial_multipliers
import Theorems.Thm_BianchiIX_partialCoreDownwardReturn_radial_response
import Theorems.Thm_BianchiIX_sech_le_exp
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
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.core_log_bound {k : ℝ} (hk : 6 ≤ k) : Real.log (4 * k) ≤ k := by
  have hk0 : 0 ≤ k := by linarith
  apply (Real.log_le_iff_le_exp (by positivity : 0 < 4 * k)).mpr
  have H := Real.quadratic_le_exp_of_nonneg hk0
  nlinarith only [hk, H, sq_nonneg (k - 6)]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restart_core_budget {h M q P ε : ℝ} (hq : 3 < q) (hP : 4 < P) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, 1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4) ≤ ε := by
  have Hq : ContinuousAt (fun r : ℝ => r ^ (q - 3)) 0 :=
    (Real.continuous_rpow_const (by linarith only [hq] : 0 ≤ q - 3)).continuousAt
  have HP : ContinuousAt (fun r : ℝ => r ^ (P - 4)) 0 :=
    (Real.continuous_rpow_const (by linarith only [hP] : 0 ≤ P - 4)).continuousAt
  have H : ContinuousAt (fun r : ℝ => 1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4)) 0 :=
    (continuousAt_const.mul Hq).add (continuousAt_const.mul HP)
  have Hzero : 1024 * h * (0 : ℝ) ^ (q - 3) + 65536 * M * (0 : ℝ) ^ (P - 4) < ε := by
    simpa only [Real.zero_rpow (by linarith only [hq] : q - 3 ≠ 0),
      Real.zero_rpow (by linarith only [hP] : P - 4 ≠ 0), mul_zero, add_zero] using hε
  exact ((H.eventually (isOpen_Iio.mem_nhds Hzero)).filter_mono nhdsWithin_le_nhds).mono
    (fun _ hr => hr.le)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restart_core_amplitude_budget {r h M q P ζ k u p ε : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hk : 0 < k) (hkr : k ≤ 32 / r)
    (hu : 0 ≤ u ∧ u ≤ 32 * h * r ^ (q - 2))
    (hp : 0 ≤ p ∧ p ≤ 2048 * M * ζ / r ^ 3) (hζ : ζ ≤ r ^ P)
    (hbudget : 1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4) ≤ ε) :
    u + p ≤ ε / k := by
  have Hsum : u + p ≤ 32 * h * r ^ (q - 2) + 2048 * M * r ^ P / r ^ 3 :=
    add_le_add hu.2 (hp.2.trans (by gcongr))
  have H := mul_le_mul hkr Hsum (add_nonneg hu.1 hp.1) (by positivity : 0 ≤ 32 / r)
  have Hq : r ^ (q - 3) = r ^ (q - 2) / r := by
    rw [show q - 3 = (q - 2) - 1 by ring, Real.rpow_sub hr, Real.rpow_one]
  have HP : r ^ (P - 4) = r ^ P / r ^ 4 := by
    simpa using Real.rpow_sub hr P (4 : ℕ)
  have Heq : 32 / r * (32 * h * r ^ (q - 2) + 2048 * M * r ^ P / r ^ 3) =
      1024 * h * r ^ (q - 3) + 65536 * M * r ^ (P - 4) := by
    rw [Hq, HP]
    field_simp
    ring
  apply (le_div_iff₀ hk).mpr
  have H' : k * (u + p) ≤ ε := ((H.trans_eq Heq).trans hbudget)
  simpa only [mul_comm k] using H'

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restart_core_sqrt_amplitude_bounds {r h M q ζ U p : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hM : 0 ≤ M) (hζ : 0 ≤ ζ)
    (hU : 0 ≤ U ∧ U ≤ 32 * h * r ^ (q - 2))
    (hp : 0 ≤ p ∧ p ≤ 2048 * M * ζ / r ^ 3) :
    Real.sqrt U ≤ Real.sqrt (32 * h) * r ^ ((q - 2) / 2) ∧
      r * Real.sqrt p ≤ Real.sqrt (2048 * M) * Real.sqrt (ζ / r) := by
  have hrpow : Real.sqrt (r ^ (q - 2)) = r ^ ((q - 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · simpa only [Real.sqrt_mul (by positivity : 0 ≤ 32 * h), hrpow] using Real.sqrt_le_sqrt hU.2
  · apply (sq_le_sq₀ (by positivity : 0 ≤ r * Real.sqrt p) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hp.1, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 2048 * M), Real.sq_sqrt (div_nonneg hζ hr.le)]
    have H := mul_le_mul_of_nonneg_left hp.2 (sq_nonneg r)
    exact H.trans_eq (by field_simp)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restart_core_sqrt_budget {r h M q ζ U p CU CP C : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hM : 0 ≤ M) (hζ : 0 ≤ ζ)
    (hU : 0 ≤ U ∧ U ≤ 32 * h * r ^ (q - 2))
    (hp : 0 ≤ p ∧ p ≤ 2048 * M * ζ / r ^ 3)
    (hCU : 0 ≤ CU) (hCP : 0 ≤ CP)
    (hC : CU * Real.sqrt (32 * h) + CP * Real.sqrt (2048 * M) ≤ C) :
    CU * Real.sqrt U + CP * r * Real.sqrt p ≤
      C * (r ^ ((q - 2) / 2) + Real.sqrt (ζ / r)) := by
  obtain ⟨HU, HP⟩ := restart_core_sqrt_amplitude_bounds hr hh hM hζ hU hp
  have H₁ := mul_le_mul_of_nonneg_left HU hCU
  have H₂ := mul_le_mul_of_nonneg_left HP hCP
  have Hcross₁ := mul_nonneg (mul_nonneg hCU (Real.sqrt_nonneg (32 * h))) (Real.sqrt_nonneg (ζ / r))
  have Hcross₂ := mul_nonneg (mul_nonneg hCP (Real.sqrt_nonneg (2048 * M))) (Real.rpow_nonneg hr.le ((q - 2) / 2))
  have HC := mul_le_mul_of_nonneg_right hC (show 0 ≤ r ^ ((q - 2) / 2) + Real.sqrt (ζ / r) by positivity)
  nlinarith only [H₁, H₂, Hcross₁, Hcross₂, HC]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restart_weak_sqrt_power {r ζ P : ℝ} (hr : 0 < r) (hζ : 0 ≤ ζ ∧ ζ ≤ r ^ P) :
    Real.sqrt (ζ / r) ≤ r ^ ((P - 1) / 2) := by
  have H : ζ / r ≤ r ^ (P - 1) := by
    rw [Real.rpow_sub hr, Real.rpow_one]
    exact div_le_div_of_nonneg_right hζ.2 hr.le
  have heq : Real.sqrt (r ^ (P - 1)) = r ^ ((P - 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    congr 1
    ring
  exact (Real.sqrt_le_sqrt H).trans_eq heq

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restart_core_cone_budget {C q P δ : ℝ}
    (hC : 0 ≤ C) (hq : 2 < q) (hP : 1 < P) (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ ζ : ℝ, 0 ≤ ζ ∧ ζ ≤ r ^ P →
      C * (r ^ ((q - 2) / 2) + Real.sqrt (ζ / r)) ≤ δ := by
  have hqpos : 0 < (q - 2) / 2 := by linarith only [hq]
  have hPpos : 0 < (P - 1) / 2 := by linarith only [hP]
  have Hq := (Real.continuous_rpow_const hqpos.le).continuousAt (x := (0 : ℝ))
  have HP := (Real.continuous_rpow_const hPpos.le).continuousAt (x := (0 : ℝ))
  have H : ContinuousAt (fun r : ℝ => C * (r ^ ((q - 2) / 2) + r ^ ((P - 1) / 2))) 0 :=
    continuousAt_const.mul (Hq.add HP)
  have Hzero : C * ((0 : ℝ) ^ ((q - 2) / 2) + (0 : ℝ) ^ ((P - 1) / 2)) < δ := by
    simpa only [Real.zero_rpow hqpos.ne', Real.zero_rpow hPpos.ne', add_zero, mul_zero] using hδ
  have HE : ∀ᶠ r : ℝ in 𝓝[>] 0,
      C * (r ^ ((q - 2) / 2) + r ^ ((P - 1) / 2)) < δ :=
    (H.eventually (isOpen_Iio.mem_nhds Hzero)).filter_mono nhdsWithin_le_nhds
  filter_upwards [HE, self_mem_nhdsWithin] with r hr hrpos
  intro ζ hζ
  exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl (restart_weak_sqrt_power hrpos hζ)) hC).trans hr.le

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

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_coordinates {m v : ℝ} (hv : 0 < v) :
    coreRadius m v / Real.cosh (coreAngle m v) = v ∧
      1 - coreRadius m v * Real.tanh (coreAngle m v) = m := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  rw [cosh_coreAngle hv, tanh_coreAngle hv]
  constructor
  · field_simp
  · field_simp
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_curve_derivative_pos {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hf0 : f x ≠ 0) (hdf : deriv f x < 0) :
    0 < deriv (fun a => 2 / f a) x := by
  have H : HasDerivAt (fun a => 2 / f a) (-2 * deriv f x / (f x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hf.hasDerivAt hf0 using 1
    ring
  rw [H.deriv]
  exact div_pos (by linarith only [hdf]) (sq_pos_of_ne_zero hf0)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_curve_identities {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) (hdf : deriv f x ≠ 0) :
    DifferentiableAt ℝ (fun a => 2 / f a) x ∧
      DifferentiableAt ℝ (fun a => 2 / g a) x ∧
      2 / g x - 2 / f x = -2 * (g x - f x) / (f x * g x) ∧
      deriv (fun a => 2 / g a) x / deriv (fun a => 2 / f a) x =
        (f x / g x) ^ 2 * (deriv g x / deriv f x) := by
  have Hf : HasDerivAt (fun a => 2 / f a) (-2 * deriv f x / (f x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hf.hasDerivAt hf0 using 1
    ring
  have Hg : HasDerivAt (fun a => 2 / g a) (-2 * deriv g x / (g x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hg.hasDerivAt hg0 using 1
    ring
  refine ⟨Hf.differentiableAt, Hg.differentiableAt, ?_, ?_⟩
  · field_simp
    ring
  · rw [Hf.deriv, Hg.deriv]
    field_simp

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

private theorem BianchiIX.coreRadius_component_bounds (m v : ℝ) :
    |m - 1| ≤ coreRadius m v ∧ |v| ≤ coreRadius m v := by
  have hr : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg v]
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (m - 1)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompact_box_bounds {x : RestartState} (hx : ‖x‖ ≤ 1 / 16) :
    |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 ∧
      246 / 256 ≤ restartRadicand x ∧ restartRadicand x ≤ 265 / 256 ∧
      15 / 16 ≤ restartCompactRoot x ∧ restartCompactRoot x ≤ 17 / 16 ∧
      -4 < restartCompactField x 0 ∧ restartCompactField x 0 < -2 := by
  have hc (i : Fin 4) : |x i| ≤ 1 / 16 := (norm_le_pi_norm x i).trans hx
  have hs (i : Fin 4) : (x i) ^ 2 ≤ 1 / 256 := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hc i)
    nlinarith only [hl, hu]
  have hm (i j : Fin 4) : |x i * x j| ≤ 1 / 256 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 16 : ℝ) * (1 / 16) := mul_le_mul (hc i) (hc j) (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hQ : |curvature (x 0) (x 2) (x 3)| ≤ 9 / 256 := by
    obtain ⟨h02l, h02u⟩ := abs_le.mp (hm 0 2)
    obtain ⟨h23l, h23u⟩ := abs_le.mp (hm 2 3)
    obtain ⟨h30l, h30u⟩ := abs_le.mp (hm 3 0)
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 3), h02u, h23u, h30u]
    · nlinarith only [hs 0, hs 2, hs 3, h02l, h23l, h30l]
  have hRl : 246 / 256 ≤ restartRadicand x := by
    dsimp only [restartRadicand]
    linarith only [hs 1, (abs_le.mp hQ).2]
  have hRu : restartRadicand x ≤ 265 / 256 := by
    dsimp only [restartRadicand]
    linarith only [sq_nonneg (x 1), (abs_le.mp hQ).1]
  have hr0 : 0 ≤ restartCompactRoot x := Real.sqrt_nonneg _
  have hr2 : restartCompactRoot x ^ 2 = restartRadicand x := Real.sq_sqrt (by linarith only [hRl])
  have hrl : 15 / 16 ≤ restartCompactRoot x := by nlinarith only [hr0, hr2, hRl]
  have hru : restartCompactRoot x ≤ 17 / 16 := by nlinarith only [hr0, hr2, hRu]
  refine ⟨hQ, hRl, hRu, hrl, hru, ?_, ?_⟩
  · change -4 < curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x
    linarith only [(abs_le.mp hQ).1, hru]
  · change curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x < -2
    linarith only [(abs_le.mp hQ).2, hrl]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.affine_mul_exp_neg_le_one (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
  simpa only [add_comm] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fromCoreAngleState_toCoreAngleState {y : ProjectiveState} (hv : 0 < y 2) :
    fromCoreAngleState (coreAngle (y 0) (y 2)) (toCoreAngleState y) = y := by
  ext i
  fin_cases i
  · exact (coreAngle_coordinates hv).2
  · rfl
  · exact (coreAngle_coordinates hv).1
  · change y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2))) = y 3
    rw [(coreAngle_coordinates hv).1]
    field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos x).le (Real.exp_pos (x / 2)).le).mpr
  rw [← Real.exp_add, add_halves]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sqrt_le_sqrt_mul_exp_half {U u x : ℝ} (hu : 0 ≤ u) (hU : U ≤ u * Real.exp x) :
    Real.sqrt U ≤ Real.sqrt u * Real.exp (x / 2) := by
  simpa only [Real.sqrt_mul hu, sqrt_exp_half] using Real.sqrt_le_sqrt hU

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partial_core_strong_log_budget {k : ℝ} (hk : 6 ≤ k) :
    Real.exp (-k / 24) * Real.log (4 * k) ≤ 24 := by
  have hk0 : 0 ≤ k := by linarith only [hk]
  have H := affine_mul_exp_neg_le_one (k / 24)
  rw [show -(k / 24) = -k / 24 by ring] at H
  have HE := Real.exp_pos (-k / 24)
  have Hk : Real.exp (-k / 24) * k ≤ 24 := by nlinarith only [H, HE]
  exact (mul_le_mul_of_nonneg_left (core_log_bound hk) HE.le).trans Hk

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partial_core_radial_cone {r K k A B D U P Uout Pout dU dP dR : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 0 ≤ K) (hk : 6 ≤ k) (hkhi : k ≤ K / r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 < D)
    (hU : 0 ≤ U) (_hP : 0 ≤ P) (hUout : 0 ≤ Uout) (hPout : 0 ≤ Pout)
    (hcontractU : Uout ≤ U * Real.exp (-k / 12)) (hcontractP : Pout ≤ P)
    (hdU : |dU| ≤ Uout * (K / r + A * Real.log (4 * k) / r ^ 2))
    (hdP : |dP| ≤ Pout * (K / r + B * Real.log (4 * k)))
    (hdR : 1 / (D * r ^ 2) ≤ |dR|) :
    |dU| ≤ (D * (K + 24 * A) * Real.sqrt U) * Real.sqrt Uout * |dR| ∧
      |dP| ≤ (D * K * (1 + B) * r * Real.sqrt P) * Real.sqrt Pout * |dR| := by
  have hr0 := hr.1
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hL : 0 ≤ Real.log (4 * k) := Real.log_nonneg (by linarith only [hk])
  have hspeed : 1 ≤ D * r ^ 2 * |dR| := by
    have H := (div_le_iff₀ (mul_pos hD (sq_pos_of_pos hr.1))).mp hdR
    nlinarith only [H]
  have hrootU : Real.sqrt Uout ≤ Real.sqrt U * Real.exp (-k / 24) := by
    simpa only [show (-k / 12) / 2 = -k / 24 by ring] using sqrt_le_sqrt_mul_exp_half hU hcontractU
  have hE : Real.exp (-k / 24) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hk0])
  have hEr : r * Real.exp (-k / 24) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hE hr.1.le).trans (by simpa only [mul_one] using hr.2)
  have HE : Real.exp (-k / 24) * (K / r + A * Real.log (4 * k) / r ^ 2) ≤
      (K + 24 * A) / r ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hr.1)).mp
    have H₁ := mul_le_mul_of_nonneg_left hEr hK
    have H₂ := mul_le_mul_of_nonneg_left (partial_core_strong_log_budget hk) hA
    calc
      _ = K * (r * Real.exp (-k / 24)) + A * (Real.exp (-k / 24) * Real.log (4 * k)) := by
        field_simp
      _ ≤ K * 1 + A * 24 := add_le_add H₁ H₂
      _ = _ := by field_simp
  have HP : K / r + B * Real.log (4 * k) ≤ K * (1 + B) / r := by
    calc
      _ ≤ K / r + B * k := add_le_add le_rfl (mul_le_mul_of_nonneg_left (core_log_bound hk) hB)
      _ ≤ K / r + B * (K / r) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hkhi hB)
      _ = _ := by ring
  have HU' : |dU| ≤ (Real.sqrt Uout * Real.sqrt U) * ((K + 24 * A) / r ^ 2) := by
    calc
      _ ≤ (Real.sqrt Uout * Real.sqrt Uout) * (K / r + A * Real.log (4 * k) / r ^ 2) := by
        rwa [Real.mul_self_sqrt hUout]
      _ ≤ (Real.sqrt Uout * (Real.sqrt U * Real.exp (-k / 24))) *
          (K / r + A * Real.log (4 * k) / r ^ 2) := by gcongr
      _ = (Real.sqrt Uout * Real.sqrt U) *
          (Real.exp (-k / 24) * (K / r + A * Real.log (4 * k) / r ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left HE (by positivity)
  have HP' : |dP| ≤ (Real.sqrt Pout * Real.sqrt P) * (K * (1 + B) / r) := by
    calc
      _ ≤ (Real.sqrt Pout * Real.sqrt Pout) * (K / r + B * Real.log (4 * k)) := by
        rwa [Real.mul_self_sqrt hPout]
      _ ≤ (Real.sqrt Pout * Real.sqrt P) * (K * (1 + B) / r) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcontractP) (Real.sqrt_nonneg _))
          HP (by positivity) (by positivity)
  constructor
  · exact HU'.trans (calc
      _ ≤ ((Real.sqrt Uout * Real.sqrt U) * ((K + 24 * A) / r ^ 2)) *
          (D * r ^ 2 * |dR|) := le_mul_of_one_le_right (by positivity) hspeed
      _ = _ := by field_simp)
  · exact HP'.trans (calc
      _ ≤ ((Real.sqrt Pout * Real.sqrt P) * (K * (1 + B) / r)) *
          (D * r ^ 2 * |dR|) := le_mul_of_one_le_right (by positivity) hspeed
      _ = _ := by field_simp)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_connection_cone_threshold :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ Real.sqrt ε ≤ 1 / 1000000 ∧ ε ≤ Real.exp (-256) := by
  let ε := min ((1 / 1000000 : ℝ) ^ 2) (Real.exp (-256))
  have hε0 : 0 < ε := lt_min (by norm_num) (Real.exp_pos _)
  have hεd : ε ≤ (1 / 1000000 : ℝ) ^ 2 := min_le_left _ _
  refine ⟨ε, hε0, ?_, ?_, min_le_right _ _⟩
  · exact hεd.trans (by norm_num)
  · exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hεd]⟩

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

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partial_core_angle_gap {k z₀ z₁ Z : ℝ} (hk : 0 < k) (hZ : 0 ≤ Z)
    (hz₀ : z₀ ≤ Z) (hz₁ : 0 ≤ z₁)
    (hentry : Real.cosh Z ≤ k / 2) (hexit : 99 / 100 * k ≤ Real.cosh z₁) :
    Real.log (99 / 50 : ℝ) ≤ z₁ - z₀ ∧ 49 / 99 ≤ z₁ - z₀ ∧ 1 / 3 < z₁ - z₀ := by
  have horder : Z ≤ z₁ := by
    have H : Real.cosh Z ≤ Real.cosh z₁ := by linarith only [hentry, hexit, hk]
    simpa only [abs_of_nonneg hZ, abs_of_nonneg hz₁] using Real.cosh_le_cosh.mp H
  have H := sech_le_exp (neg_le_neg horder)
  rw [Real.cosh_neg, Real.cosh_neg, show -Z - -z₁ = z₁ - Z by ring] at H
  have H' : 1 / Real.cosh Z ≤ Real.exp (z₁ - Z) / Real.cosh z₁ := by
    simpa only [one_div_mul_eq_div] using H
  have Hmul := (div_le_div_iff₀ (Real.cosh_pos Z) (Real.cosh_pos z₁)).mp H'
  have Hratio : (99 / 50 : ℝ) ≤ Real.exp (z₁ - Z) := by
    apply (mul_le_mul_iff_right₀ (Real.cosh_pos Z)).mp
    nlinarith only [hentry, hexit, Hmul]
  have Hlog : Real.log (99 / 50 : ℝ) ≤ z₁ - Z :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr Hratio
  have Hnum : (49 / 99 : ℝ) ≤ Real.log (99 / 50 : ℝ) := by
    have H := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 99 / 50)
    norm_num at H
    linarith only [H]
  refine ⟨by linarith only [Hlog, hz₀], by linarith only [Hnum, Hlog, hz₀], ?_⟩
  linarith only [Hnum, Hlog, hz₀]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionChart_constraint {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 ≤ restartSectionRadicand h Z) : stateConstraint (restartSectionChart h Z) = 1 := by
  have H := Real.sq_sqrt hZ
  dsimp [stateConstraint, constraint, shearSq, restartSectionChart]
  rw [neg_sq, H]
  unfold restartSectionRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartCenterProjection_section (h : ℝ) (Z : RestartCenterState) :
    restartCenterProjection (restartSectionChart h Z) = Z := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysicalCoordinates_norm_le {x : NormalizedState} {R : ℝ} (hR : 0 ≤ R)
    (hn : |x 2| ≤ R) (hZ : ‖restartCenterProjection x‖ ≤ R) :
    ‖restartPhysicalCoordinates x‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact hn
  · exact (norm_le_pi_norm (restartCenterProjection x) 0).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 1).trans hZ
  · exact (norm_le_pi_norm (restartCenterProjection x) 2).trans hZ

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

private theorem BianchiIX.coreAngle_abs_le_arcosh {m v : ℝ} (hv : 1 ≤ v) :
    |coreAngle m v| ≤ Real.arcosh (coreRadius m v) := by
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hk0 := coreRadius_pos (m := m) hv0
  have Hcosh : Real.cosh (coreAngle m v) ≤ coreRadius m v := by
    rw [cosh_coreAngle hv0]
    exact div_le_self hk0.le hv
  have H := (Real.arcosh_le_arcosh (Real.cosh_pos _) hk0).mpr Hcosh
  rw [← Real.cosh_abs (coreAngle m v), Real.arcosh_cosh (abs_nonneg _)] at H
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partialCoreEntry_region {y : ProjectiveState} {ε : ℝ}
    (hk : 6 ≤ coreRadius (y 0) (y 2)) (hv : 1 ≤ y 2)
    (hu : 0 ≤ y 1) (hp : 0 ≤ y 2 * y 3)
    (hε : ε ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ ε / coreRadius (y 0) (y 2)) :
    coreRegion (coreRadius (y 0) (y 2)) y := by
  have hk0 : 0 < coreRadius (y 0) (y 2) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk
  have Hcap := hsmall.trans (div_le_div_of_nonneg_right hε hk0.le)
  refine ⟨?_, hv, ⟨hu, ?_⟩, ⟨hp, ?_⟩⟩
  · rw [coreRadius_sq, sub_self, abs_zero]
    norm_num
  · linarith only [Hcap, hp]
  · linarith only [Hcap, hu]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_normalized_partialCore_firstReturn {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → (1 < β s 2 ∨ (β s 2 = 1 ∧ 1 ≤ β s 0)) →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k) →
    ∃ t > s, IsLeast {u | s < u ∧ β u 2 = 1} t ∧
      β t 0 < 1 ∧ 0 < coreAngle (β t 0) (β t 2) ∧
      deriv (fun u => β u 2) t ≤ -(1 + normalizedMaxCurve x t₀ t 0) * k / 2 ∧
      t - s ≤ 2 * k * Real.log (4 * k) ∧ ∀ u ∈ Icc s t,
        3 / (2 * k ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u) ∧
        |coreRadius (β u 0) (β u 2) - k| ≤ 16 * (β s 1 + (β s 2 * β s 3) ^ 2 / k) ∧
        |coreRadius (β u 0) (β u 2) ^ 2 - k ^ 2| < 1 / 16 := by
  intro β hR hVcase hU hP
  obtain ⟨t, hst, hvt, H⟩ := exists_normalized_partialCore_return hc hk hs hA hR hVcase hU hP
  have hk0 : 0 < k := by linarith only [hk]
  have hpos (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H u hu).1
  have hr (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_radius_bounds hk (H u hu).2
  have hv (u : ℝ) (hu : u ∈ Icc s t) : 1 ≤ β u 2 := (H u hu).2.2.1
  have hwall (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_wall_bounds (H u hu).2
  have hleast := normalized_core_return_isLeast hc hk hs hst hpos
    (fun u hu => (hr u hu).1) hv (fun u hu => (hwall u hu).1) (fun u hu => (hwall u hu).2) hvt
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hdown := normalized_core_return_downward hc hk hs hst (hpos t htm) hvt
    (fun u hu => hv u ⟨hu.1.le, hu.2.le⟩) (hr t htm).1 (hwall t htm).1 (hwall t htm).2
  have htime := (normalized_core_residence hc hk hs hst.le hpos hr hv
    (fun u hu => (hwall u hu).1) (fun u hu => (hwall u hu).2)).2
  refine ⟨t, hst, hleast, hdown.1, hdown.2.1, hdown.2.2.1, htime, ?_⟩
  intro u hu
  have hsub : Icc s u ⊆ Icc s t := fun v hv => ⟨hv.1, hv.2.trans hu.2⟩
  have Henergy := normalized_partialCore_energy_band_improves hc hk hs hu.1
    (fun v hv => hpos v (hsub hv)) hR
    (fun v hv => by rw [coreRadius_sq]; exact (H v (hsub hv)).2.1)
    (fun v hv' => hv v (hsub hv')) (fun v hv => (H v (hsub hv)).2.2.2.1)
    (fun v hv => (H v (hsub hv)).2.2.2.2)
  exact ⟨(H u hu).1, (H u hu).2, Henergy⟩

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
open Set

private theorem BianchiIX.normalized_partialCore_exit_contraction {x : NormalizedState} {t₀ s t k Z : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s < t)
    (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, coreRegion k (β u)) →
    coreAngle (β s 0) (β s 2) ≤ Z → β t 2 = 1 →
    Real.log (99 / 50 : ℝ) ≤ coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2) ∧
      49 / 99 ≤ coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2) ∧
      β t 1 ≤ β s 1 * Real.exp (-k / 12) ∧ β t 3 ≤ β s 2 * β s 3 := by
  intro β hregion hz₀ hvt
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hk0 : 0 < k := by linarith only [hk]
  have hr (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_radius_bounds hk (hregion u hu)
  have hw (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_wall_bounds (hregion u hu)
  have hv (u : ℝ) (hu : u ∈ Icc s t) : 1 ≤ β u 2 := (hregion u hu).2.1
  have hout := normalized_core_return_downward hc hk hs hst (hA t htm) hvt
    (fun u hu => hv u ⟨hu.1.le, hu.2.le⟩) (hr t htm).1 (hw t htm).1 (hw t htm).2
  have hcosh : 99 / 100 * k ≤ Real.cosh (coreAngle (β t 0) (β t 2)) := by
    rw [cosh_coreAngle (zero_lt_one.trans_le (hv t htm)), hvt, div_one]
    simpa only [hvt] using (hr t htm).1
  obtain ⟨hgap, hgap', hgap3⟩ := partial_core_angle_gap hk0 hZ hz₀ hout.2.1.le
    (by linarith only [hkZ]) hcosh
  have hdom : Icc s t ⊆ normalizedMaxDomain x t₀ := fun _ hu =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  obtain ⟨hU, hP⟩ := normalized_core_prefix_contraction hk (convex_Icc s t) hdom hc hA
    hsm htm hst.le (fun u hu => (hr u hu).1) hv
    (fun u hu => (hw u hu).1) (fun u hu => (hw u hu).2)
  have hexp : -k * (coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) / 4 ≤ -k / 12 := by
    have H := mul_le_mul_of_nonneg_left hgap3.le hk0.le
    linarith only [H]
  change β t 2 * β t 3 ≤ β s 2 * β s 3 at hP
  rw [hvt, one_mul] at hP
  exact ⟨hgap, hgap', hU.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (hw s hsm).1.1), hP⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionRadicand_pos_of_small {h : ℝ} {Z : RestartCenterState}
    (hh : |h| ≤ 1 / 16) (hZ : ‖Z‖ ≤ 1 / 16) : 0 < restartSectionRadicand h Z := by
  have hw := restartPhysicalCoordinates_norm_le (x := restartSectionChart h Z) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hh (by rwa [restartCenterProjection_section])
  have H := (restartCompact_box_bounds hw).2.1
  change 246 / 256 ≤ restartSectionRadicand h Z at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionChart {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) Z := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt hZ.ne').neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) Z
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) Z
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) Z

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardReturnTime_eq {y : ProjectiveState} {T : ℝ}
    (hT : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0} T) :
    partialCoreDownwardReturnTime y = T := hT.csInf_eq

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardReturnTime_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
      projectiveOriginalFlow z 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0} (τ z)) :
    partialCoreDownwardReturnTime =ᶠ[𝓝 y] τ := hτ.mono fun _ h => partialCoreDownwardReturnTime_eq h

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardReturn_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} (partialCoreDownwardReturnTime y) ∧
      ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
      (∀ᶠ z in 𝓝 y,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          projectiveOriginalFlow z 0 t 2 = 1 ∧
          normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
            (partialCoreDownwardReturnTime z) ∧
        ∀ t ∈ Icc 0 (partialCoreDownwardReturnTime z), t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 t 0) ∧
      ∀ w : ProjectiveState,
        let v := fderiv ℝ toCoreAngleState y w
        let dz := fderiv ℝ projectiveCoreAngle y w
        |(fderiv ℝ partialCoreDownwardReturnState y w) 0 - v 0| ≤ 4096 * coreVariationBound *
          (|v 1| + (y 1 + y 2 * y 3) * (|v 0| + |v 2|) / k +
            (k * y 1 + (y 2 * y 3) ^ 2 / k) * |dz|) := by
  obtain ⟨T, _, hfirst, τ, hτ, hcτ, hnear, hcF, Hbound⟩ :=
    exists_partialCore_downward_radius_response hk hy hR hV
  have heq := partialCoreDownwardReturnTime_eventuallyEq (hnear.mono fun _ h => h.1)
  have hstate : partialCoreDownwardReturnState =ᶠ[𝓝 y] fun z =>
      toCoreAngleState (projectiveOriginalFlow z 0 (τ z)) := by
    filter_upwards [heq] with z hz
    simp only [partialCoreDownwardReturnState, hz]
  refine ⟨?_, hcτ.congr_of_eventuallyEq heq, hcF.congr_of_eventuallyEq hstate, ?_, ?_⟩
  · rw [heq.self_of_nhds, hτ]
    exact hfirst
  · filter_upwards [hnear, heq] with z hz ht
    simpa only [ht] using hz
  · intro w
    rw [hstate.fderiv_eq]
    exact Hbound w

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCoreDownwardReturn_bounds {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    let T := partialCoreDownwardReturnTime y
    projectiveOriginalFlow y 0 T 0 < 1 ∧ T ≤ 2 * k * Real.log (4 * k) ∧
      ∀ t ∈ Icc 0 T,
        0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
        coreRegion k (projectiveOriginalFlow y 0 t) ∧
        |coreRadius (projectiveOriginalFlow y 0 t 0) (projectiveOriginalFlow y 0 t 2) - k| ≤
          16 * (y 1 + (y 2 * y 3) ^ 2 / k) ∧
        |coreRadius (projectiveOriginalFlow y 0 t 0) (projectiveOriginalFlow y 0 t 2) ^ 2 - k ^ 2| < 1 / 16 := by
  intro T
  have hk0 : 0 < k := by linarith only [hk]
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  let β := projectiveOriginalFlow y 0
  have hzero : β 0 = y := projectiveOriginalFlow_initial hD 0
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hR0 : coreRadius (β 0 0) (β 0 2) = k := by rw [hzero]; exact hR
  have hV0 : 1 < β 0 2 ∨ (β 0 2 = 1 ∧ 1 ≤ β 0 0) := by rw [hzero]; exact hV
  have hU0 : 0 ≤ β 0 1 ∧ β 0 1 ≤ (1 / 10000) / k := by rw [hzero]; exact hy.2.2.1
  have hP0 : 0 ≤ β 0 2 * β 0 3 ∧ β 0 2 * β 0 3 ≤ (1 / 10000) / k := by
    rw [hzero]; exact hy.2.2.2
  obtain ⟨S, _, hfirstS, hM, _, _, htime, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk le_rfl hA hR0 hV0 hU0 hP0
  have hST : S = T := hfirstS.unique (partialCoreDownwardReturn_regular hk hy hR hV).1
  rw [hST] at hM htime H
  refine ⟨hM, by simpa only [sub_zero] using htime, ?_⟩
  intro t ht
  have Ht := H t ht
  change _ ∧ _ ∧ |coreRadius (β t 0) (β t 2) - k| ≤
    16 * (β 0 1 + (β 0 2 * β 0 3) ^ 2 / k) ∧ _ at Ht
  rw [hzero] at Ht
  exact ⟨lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) Ht.1, Ht.2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_connectionReturnPhysicalState {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    ContDiffAt ℝ 2 connectionReturnPhysicalState p := by
  have hstate := (connectionReturn_regular hμ hu hw).2.2.1
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · have hm := contDiffAt_pi.mp hstate 0
    exact ((((hm.neg.sub contDiffAt_const).pow 2).add contDiffAt_const).sqrt (by positivity))
  · exact contDiffAt_pi.mp hstate 1
  · exact contDiffAt_pi.mp hstate 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_coreExitConnectionParameters (n : WithTop ℕ∞) {Z : CoreAngleState} (hK : 1 < Z 0) :
    ContDiffAt ℝ n coreExitConnectionParameters Z := by
  have hs : Z 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hK] : 0 < Z 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreExitConnectionParameters] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_of_constraint {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartProjectionHeight (x 2, ![x 1, x 3, x 4]) = 1 + x 0 := by
  have hd : restartProjectionDefect (x 2, ![x 1, x 3, x 4]) = 1 - (x 0) ^ 2 := by
    change (x 1) ^ 2 + curvature (x 2) (x 3) (x 4) = _
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  have hden : 1 - x 0 ≠ 0 := by linarith only [hp]
  rw [restartProjectionHeight, hd, show 1 - (1 - (x 0) ^ 2) = (x 0) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_neg hp]
  change (1 - x 0 ^ 2) / (1 - x 0) = 1 + x 0
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCoreDownwardReturn_contraction {k Z : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0))
    (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k) (hz : projectiveCoreAngle y ≤ Z) :
    let T := partialCoreDownwardReturnTime y
    projectiveOriginalFlow y 0 T 1 ≤ y 1 * Real.exp (-k / 12) ∧
      projectiveOriginalFlow y 0 T 3 ≤ y 2 * y 3 := by
  intro T
  have HR := partialCoreDownwardReturn_regular hk hy hR hV
  have HB := (partialCoreDownwardReturn_bounds hk hy hR hV).2.2
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have hzero := projectiveOriginalFlow_initial hD (0 : ℝ)
  have hz0 : coreAngle (projectiveOriginalFlow y 0 0 0) (projectiveOriginalFlow y 0 0 2) ≤ Z := by
    rw [hzero]; exact hz
  have H := normalized_partialCore_exit_contraction hc hk le_rfl HR.1.1.1 hZ hkZ
    (fun t ht => (HB t ht).1) (fun t ht => (HB t ht).2.1) hz0 HR.1.1.2
  have HC := H.2.2
  change projectiveOriginalFlow y 0 T 1 ≤ projectiveOriginalFlow y 0 0 1 * Real.exp (-k / 12) ∧
    projectiveOriginalFlow y 0 T 3 ≤ projectiveOriginalFlow y 0 0 2 * projectiveOriginalFlow y 0 0 3 at HC
  rwa [hzero] at HC

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCoreDownwardReturn_radial_cone {Y : ℝ → ProjectiveState} {x r K D Z : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hD : 0 < D) (hZ : 0 ≤ Z)
    (hY : DifferentiableAt ℝ Y x) :
    let k := fun a => coreRadius (Y a 0) (Y a 2)
    let U := fun a => Y a 1
    let p := fun a => Y a 2 * Y a 3
    let z := fun a => projectiveCoreAngle (Y a)
    let A := (200 * coreVariationBound + 2) * K ^ 2
    let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
    let τ := partialCoreDownwardReturnTime
    let f := fun a => partialCoreDownwardReturnState (Y a) 0
    let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
    let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
    6 ≤ k x → coreRegion (k x) (Y x) → (1 < Y x 2 ∨ (Y x 2 = 1 ∧ 1 ≤ Y x 0)) →
    2 * Real.cosh Z ≤ k x → z x ≤ Z →
    2 / (K * r) ≤ k x → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
    1 / (D * r ^ 2) ≤ -deriv k x →
    |deriv U x| ≤ K * U x / r → |deriv p x| ≤ K * p x / r → |deriv z x| ≤ K / r →
    4 * (4096 * coreVariationBound) * K ^ 2 * (U x + r * p x) ≤ 1 / (2 * D) →
    DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ fU x ∧ DifferentiableAt ℝ fP x ∧
    1 / (2 * D * r ^ 2) ≤ -deriv f x ∧ |deriv f x| ≤ (K + 1 / (2 * D)) / r ^ 2 ∧
    0 ≤ fU x ∧ 0 ≤ fP x ∧ fU x ≤ U x * Real.exp (-k x / 12) ∧ fP x ≤ p x ∧
    |deriv fU x| ≤ (2 * D * (K + 24 * A) * Real.sqrt (U x)) * Real.sqrt (fU x) * |deriv f x| ∧
    |deriv fP x| ≤ (2 * D * K * (1 + B) * r * Real.sqrt (p x)) * Real.sqrt (fP x) * |deriv f x| ∧
    (U x = 0 → fU x = 0 ∧ deriv fU x = 0) ∧
    (p x = 0 → fP x = 0 ∧ deriv fP x = 0) := by
  intro k U p z A B τ f fU fP hk hy hV hkZ hz hklo hkhi hdk hdklo hdU hdp hdz hsmall
  have hr0 := hr.1
  have hK0 : 0 < K := by linarith only [hK]
  have hk0 : 0 < k x := by linarith only [hk]
  have hki : 1 / k x ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    nlinarith only [H]
  obtain ⟨hf, _, _, _, _, hde, _⟩ := partialCoreDownwardReturn_radial_response hr hK hY
    hk hy hV hklo hkhi hdk hdU hdp hdz
  have hkd : DifferentiableAt ℝ k x := by
    have H := ((contDiffAt_toCoreAngleState 1 (zero_lt_one.trans_le hy.2.1)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
    exact (hasDerivAt_pi.mp H 0).differentiableAt
  change DifferentiableAt ℝ f x at hf
  change |deriv (fun a => f a - k a) x| ≤
    4 * (4096 * coreVariationBound) * K ^ 2 * (U x + r * p x) / r ^ 2 at hde
  rw [deriv_fun_sub hf hkd] at hde
  have he : |deriv f x - deriv k x| ≤ 1 / (2 * D * r ^ 2) := hde.trans
    ((div_le_div_of_nonneg_right hsmall (sq_nonneg r)).trans_eq (by ring))
  have hslope : 1 / (2 * D * r ^ 2) ≤ -deriv f x := by
    have H := (abs_le.mp he).2
    have heq : 1 / (D * r ^ 2) = 2 * (1 / (2 * D * r ^ 2)) := by ring
    rw [heq] at hdklo
    linarith only [H, hdklo]
  have hfhi : |deriv f x| ≤ (K + 1 / (2 * D)) / r ^ 2 := by
    calc
      _ = |deriv k x + (deriv f x - deriv k x)| := by congr 1; ring
      _ ≤ |deriv k x| + |deriv f x - deriv k x| := abs_add_le _ _
      _ ≤ K / r ^ 2 + 1 / (2 * D * r ^ 2) := add_le_add hdk he
      _ = _ := by ring
  obtain ⟨_, _, _, _, _, hDU, hDP, hu0, hp0, hdu, hdpout, hzeroU, hzeroP⟩ :=
    partialCoreDownwardReturn_radial_multipliers hr hK hY hk hy hV hki hkhi hdk hdU hdp hdz
  have HC := partialCoreDownwardReturn_contraction hk hy rfl hV hZ hkZ hz
  have hA : 0 ≤ A := by dsimp only [A, coreVariationBound]; positivity
  have hB : 0 ≤ B := by dsimp only [B, coreVariationBound]; positivity
  have Hcone := partial_core_radial_cone hr hK0.le hk hkhi hA hB (by positivity : 0 < 2 * D)
    hy.2.2.1.1 hy.2.2.2.1 hu0 hp0 HC.1 HC.2 hdu hdpout (hslope.trans (neg_le_abs _))
  exact ⟨hf, hDU, hDP, hslope, hfhi, hu0, hp0, HC.1, HC.2, Hcone.1, Hcone.2, hzeroU, hzeroP⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionDefect {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t) :
    HasDerivAt (fun x => restartProjectionDefect (p x))
      (restartProjectionDefectTangent (p t) v) t := by
  have Hn : HasDerivAt (fun x => (p x).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have Hc (i : Fin 3) : HasDerivAt (fun x => (p x).2 i) (v.2 i) t := by
    let P : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact P.hasFDerivAt.comp_hasDerivAt t
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H)
  have HD := ((Hc 0).pow 2).add
    ((((Hn.pow 2).add ((Hc 1).pow 2)).add ((Hc 2).pow 2)).const_mul 2)
  have HD' := HD.sub (((Hn.add (Hc 1)).add (Hc 2)).pow 2)
  convert! HD' using 1
  · funext x
    dsimp [restartProjectionDefect, curvature]
    ring
  · dsimp [restartProjectionDefectTangent]
    ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionDefectTangent_bound {p v : RestartRadialState} {R D : ℝ}
    (hp : ‖p‖ ≤ R) (hv : ‖v‖ ≤ D) :
    |restartProjectionDefectTangent p v| ≤ 32 * R * D := by
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have hD : 0 ≤ D := (norm_nonneg v).trans hv
  have pn : |p.1| ≤ R := (norm_fst_le p).trans hp
  have pc (i : Fin 3) : |p.2 i| ≤ R := (norm_le_pi_norm p.2 i).trans ((norm_snd_le p).trans hp)
  have vn : |v.1| ≤ D := (norm_fst_le v).trans hv
  have vc (i : Fin 3) : |v.2 i| ≤ D := (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have ps : |p.1 + p.2 1 + p.2 2| ≤ 3 * R :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [pn, pc 1, pc 2])
  have vs : |v.1 + v.2 1 + v.2 2| ≤ 3 * D :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only [vn, vc 1, vc 2])
  have Hsum : |p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2| ≤ 3 * R * D := by
    calc
      _ ≤ |p.1 * v.1| + |p.2 1 * v.2 1| + |p.2 2 * v.2 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ R * D + R * D + R * D := by
        simp only [abs_mul]
        gcongr
        · exact pc 1
        · exact vc 1
        · exact pc 2
        · exact vc 2
      _ = _ := by ring
  unfold restartProjectionDefectTangent
  calc
    _ ≤ |2 * p.2 0 * v.2 0| + |4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
        |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
      have HT : |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2) -
          2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| ≤
          |2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)| +
          |2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)| := by
        simpa using (abs_sub_le (2 * p.2 0 * v.2 0 + 4 *
          (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2)) 0
          (2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)))
      exact HT.trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * R * D + 4 * (3 * R * D) + 2 * (3 * R) * (3 * D) := by
      norm_num only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      gcongr
      · exact pc 0
      · exact vc 0
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_eq_sqrt {p : RestartRadialState}
    (hd : restartProjectionDefect p ≤ 1) :
    restartProjectionHeight p = 1 - Real.sqrt (1 - restartProjectionDefect p) := by
  have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect p)
  apply (div_eq_iff (by positivity : 1 + Real.sqrt (1 - restartProjectionDefect p) ≠ 0)).mpr
  nlinarith only [Hsq]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartProjectionHeight {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) < 1) :
    HasDerivAt (fun x => restartProjectionHeight (p x))
      (restartProjectionDefectTangent (p t) v / (2 * Real.sqrt (1 - restartProjectionDefect (p t)))) t := by
  have HD := hasDerivAt_restartProjectionDefect H
  have HS := ((HD.const_sub 1).sqrt (by linarith only [hd] : 1 - restartProjectionDefect (p t) ≠ 0)).const_sub 1
  have Heq : (fun x => restartProjectionHeight (p x)) =ᶠ[𝓝 t]
      fun x => 1 - Real.sqrt (1 - restartProjectionDefect (p x)) := by
    filter_upwards [HD.continuousAt.eventually (isOpen_Iio.mem_nhds hd)] with x hx
    exact restartProjectionHeight_eq_sqrt hx.le
  convert! HS.congr_of_eventuallyEq Heq using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartProjectionHeight_derivative_bound {p : ℝ → RestartRadialState}
    {v : RestartRadialState} {t R D : ℝ} (H : HasDerivAt p v t)
    (hd : restartProjectionDefect (p t) ≤ 1 / 2) (hp : ‖p t‖ ≤ R) (hv : ‖v‖ ≤ D) :
    DifferentiableAt ℝ (fun x => restartProjectionHeight (p x)) t ∧
      |deriv (fun x => restartProjectionHeight (p x)) t| ≤ 32 * R * D := by
  have HD := hasDerivAt_restartProjectionHeight H (by linarith only [hd])
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv, abs_div, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt (1 - restartProjectionDefect (p t)))]
  have hsqrt : 1 / 2 ≤ Real.sqrt (1 - restartProjectionDefect (p t)) := by
    have Hsq := Real.sq_sqrt (by linarith only [hd] : 0 ≤ 1 - restartProjectionDefect (p t))
    nlinarith only [Hsq, Real.sqrt_nonneg (1 - restartProjectionDefect (p t)), hd]
  exact (div_le_self (abs_nonneg _) (by linarith only [hsqrt])).trans
    (restartProjectionDefectTangent_bound hp hv)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardReturn_connectionParameters_eventuallyEq {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    let out := fun z => projectiveOriginalFlow z 0 (partialCoreDownwardReturnTime z)
    (fun z => coreExitConnectionParameters ![coreRadius (out z 0) (out z 2), out z 1, out z 3]) =ᶠ[𝓝 y]
      (fun z => coreExitConnectionParameters (partialCoreDownwardReturnState z)) := by
  intro out
  filter_upwards [(partialCoreDownwardReturn_regular hk hy hR hV).2.2.2.1] with z hz
  have hhit : out z 2 = 1 := hz.1.1.2.2.1
  apply congrArg coreExitConnectionParameters
  ext i
  fin_cases i
  · rfl
  · rfl
  · change out z 3 = out z 2 * out z 3
    rw [hhit, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardConnection_regular {k Z ε : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hz : projectiveCoreAngle y ≤ Z) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < y 1 ∧ y 1 ≤ ε / k) (hp : 0 < y 2 * y 3 ∧ y 2 * y 3 ≤ ε / k) :
    let p := fun x => coreExitConnectionParameters (partialCoreDownwardReturnState x)
    ContDiffAt ℝ 2 p y ∧
      ContDiffAt ℝ 2 (fun x => partialCoreDownwardReturnTime x + connectionReturnTime (p x)) y ∧
      ContDiffAt ℝ 2 (fun x => connectionReturnState (p x)) y := by
  intro p
  have HR := partialCoreDownwardReturn_regular hk hy hR hV
  obtain ⟨_, _, _, _, _, _, _, _, _, hct, hcs, _⟩ :=
    partialCoreDownwardReturn_connection_domain hk hy hR hV hZ hkZ hz hε hu hp
  have HB := (partialCoreDownwardReturn_bounds hk hy hR hV).2.2 _ ⟨HR.1.1.1.le, le_rfl⟩
  have hr := (coreRegion_radius_bounds hk HB.2.1).1
  have hf : 1 < partialCoreDownwardReturnState y 0 :=
    lt_of_lt_of_le (by linarith only [hk] : 1 < 99 / 100 * k) hr
  have hcP : ContDiffAt ℝ 2 p y := (contDiffAt_coreExitConnectionParameters 2 hf).comp y HR.2.2.1
  exact ⟨hcP, HR.2.1.add (ContDiffAt.comp (g := connectionReturnTime) (f := p) y hct hcP),
    ContDiffAt.comp (g := connectionReturnState) (f := p) y hcs hcP⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionDefect_shear_bounds {p : RestartRadialState} {a σ : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 128) (hσ : |σ| = 1)
    (hs : 3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ a ^ 2)
    (h₂ : 0 ≤ p.2 1 ∧ p.2 1 ≤ a / 16) (h₃ : 0 ≤ p.2 2 ∧ p.2 2 ≤ a / 16) :
    a ^ 2 / 2 ≤ restartProjectionDefect p ∧ restartProjectionDefect p ≤ 6 * a ^ 2 := by
  have hsig : σ ^ 2 = 1 := by nlinarith only [sq_abs σ, hσ]
  have hsq : (σ * p.2 0) ^ 2 = (p.2 0) ^ 2 := by rw [mul_pow, hsig, one_mul]
  have hslo := pow_le_pow_left₀ (by positivity [ha.1] : 0 ≤ 3 * a / 4) hs.1 2
  have hshi := pow_le_pow_left₀ (by linarith only [hs.1, ha.1] : 0 ≤ σ * p.2 0) hs.2 2
  rw [hsq] at hslo hshi
  have hsum : p.2 1 + p.2 2 ≤ a / 8 := by linarith only [h₂.2, h₃.2]
  have hcross := mul_le_mul hn.2 hsum (add_nonneg h₂.1 h₃.1) (sq_nonneg a)
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have ha3 : a ^ 2 * a ≤ a ^ 2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 (sq_nonneg a)
  have hnsq := pow_le_pow_left₀ hn.1 hn.2 2
  have hdiff : |p.2 1 - p.2 2| ≤ a / 16 :=
    abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩
  have hdsq := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  rw [sq_abs] at hdsq
  have heq : restartProjectionDefect p = (p.2 0) ^ 2 + p.1 ^ 2 + (p.2 1 - p.2 2) ^ 2 -
      2 * p.1 * (p.2 1 + p.2 2) := by unfold restartProjectionDefect curvature; ring
  constructor
  · rw [heq]
    have ha3small := mul_le_mul_of_nonneg_left ha.2 (sq_nonneg a)
    nlinarith only [hslo, hcross, ha3small, sq_nonneg p.1, sq_nonneg (p.2 1 - p.2 2), sq_nonneg a]
  · rw [heq]
    have hneg := mul_nonneg hn.1 (add_nonneg h₂.1 h₃.1)
    have hnsmall := mul_le_mul_of_nonneg_left ha.2 ha.1.le
    have hn4small := mul_le_mul_of_nonneg_left hnsmall (sq_nonneg a)
    nlinarith only [hshi, hnsq, hn4small, hdsq, hneg, ha3, sq_nonneg a]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartProjectionHeight_shear_bounds {p : RestartRadialState} {a σ : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 128) (hσ : |σ| = 1)
    (hs : 3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ a ^ 2)
    (h₂ : 0 ≤ p.2 1 ∧ p.2 1 ≤ a / 16) (h₃ : 0 ≤ p.2 2 ∧ p.2 2 ≤ a / 16) :
    restartProjectionDefect p ≤ 1 / 2 ∧
      a ^ 2 / 4 ≤ restartProjectionHeight p ∧ restartProjectionHeight p ≤ 6 * a ^ 2 := by
  obtain ⟨Hlo, Hhi⟩ := restartProjectionDefect_shear_bounds ha hσ hs hn h₂ h₃
  have hd0 : 0 ≤ restartProjectionDefect p := le_trans (by positivity) Hlo
  have hd1 : restartProjectionDefect p ≤ 1 / 2 := by nlinarith only [Hhi, ha.1, ha.2]
  have hsqrt := Real.sqrt_nonneg (1 - restartProjectionDefect p)
  have hsqrt1 : Real.sqrt (1 - restartProjectionDefect p) ≤ 1 := by rw [Real.sqrt_le_one]; linarith only [hd0]
  have hden : 0 < 1 + Real.sqrt (1 - restartProjectionDefect p) := by positivity
  refine ⟨hd1, (le_div_iff₀ hden).mpr ?_, (div_le_iff₀ hden).mpr ?_⟩
  · nlinarith only [Hlo, mul_le_mul_of_nonneg_left hsqrt1 (sq_nonneg a)]
  · nlinarith only [Hhi, mul_nonneg (sq_nonneg a) hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartShearCurve (σ n₂ n₃ ρ : ℝ) :
    HasDerivAt (restartShearCurve σ n₂ n₃) (restartShearDirection σ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartShearCurve, restartShearDirection] using (hasDerivAt_id ρ).const_mul σ
  · convert! hasDerivAt_const ρ n₂ using 1
  · convert! hasDerivAt_const ρ n₃ using 1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartShearCurve_annulus {a ρ σ ε n₂ n₃ : ℝ} (ha : 0 < a)
    (hρ : ρ ∈ Icc a (2 * a)) (hσ : |σ| = 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 64)
    (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) :
    ‖restartShearCurve σ n₂ n₃ ρ‖ ≤ 2 * a ∧
      a ≤ restartRadialNorm (restartShearCurve σ n₂ n₃ ρ) ∧ |n₂ - n₃| ≤ 2 * ε * a := by
  have hρpos := ha.trans_le hρ.1
  have hsmall : 2 * ε * a ≤ 2 * a := by nlinarith only [hε.2, ha]
  refine ⟨?_, ?_, abs_le.mpr ⟨by linarith only [h₂.1, h₃.2], by linarith only [h₃.1, h₂.2]⟩⟩
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * a)).mpr
    intro i
    fin_cases i
    · change |σ * ρ| ≤ 2 * a
      simpa only [abs_mul, hσ, abs_of_pos hρpos, one_mul] using hρ.2
    · exact (show |n₂| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₂.1] using h₂.2).trans hsmall
    · exact (show |n₃| ≤ 2 * ε * a by simpa only [abs_of_nonneg h₃.1] using h₃.2).trans hsmall
  · have H := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (n₂ - n₃)) :
        (σ * ρ) ^ 2 ≤ (σ * ρ) ^ 2 + (n₂ - n₃) ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_mul, hσ, abs_of_pos hρpos, one_mul] at H
    exact hρ.1.trans H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restartSectionProjectionHeight_eq {h T : ℝ} {Z : RestartCenterState}
    (hrad : 0 < restartSectionRadicand h Z) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h Z) 0 T 0 < 0) :
    (fun W => restartProjectionHeight (restartSectionRadialState h T W)) =ᶠ[𝓝 Z]
      (fun W => 1 + normalizedMaxCurve (restartSectionChart h W) 0 T 0) := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have Hchart := (contDiffAt_restartSectionChart hrad 1).continuousAt
  have Hflow := (hasFDerivAt_normalizedMaxCurve_initial hdom).continuousAt.comp Hchart
  have Hcoord : ContinuousAt (fun W => normalizedMaxCurve (restartSectionChart h W) 0 T 0) Z :=
    (continuous_apply 0).continuousAt.comp Hflow
  have HR : ContinuousAt (restartSectionRadicand h) Z := by
    unfold restartSectionRadicand curvature
    fun_prop
  filter_upwards [HR.eventually (isOpen_Ioi.mem_nhds hrad),
    Hcoord.eventually (isOpen_Iio.mem_nhds hneg)] with W hW hN
  have HC := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hW.le) hT).2.1
  exact restartProjectionHeight_of_constraint HC hN

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartFastShearProjectiveEntry_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε σ n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := q / 2 * Real.log (1 / a)
          let y := restartFastShearProjectiveEntry h T σ n₂ n₃ ρ
          T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
          DifferentiableAt ℝ (restartFastShearProjectiveEntry h T σ n₂ n₃) ρ ∧
          DifferentiableAt ℝ (restartFastShearHeight h T σ n₂ n₃) ρ ∧
          a ^ 2 / 4 ≤ restartFastShearHeight h T σ n₂ n₃ ρ ∧
          restartFastShearHeight h T σ n₂ n₃ ρ ≤ 6 * a ^ 2 ∧
          |deriv (restartFastShearHeight h T σ n₂ n₃) ρ| ≤ 512 * a ∧
          (1 / (8 * a) ≤ σ * y 0 ∧ σ * y 0 ≤ 18 / a) ∧
          (0 < y 1 ∧ y 1 ≤ 8 * h * a ^ (q - 2)) ∧
          (n₂ / (12 * a ^ 2) ≤ y 2 ∧ y 2 ≤ 16 * n₂ / a ^ 2) ∧
          (n₃ / (12 * a ^ 2) ≤ y 3 ∧ y 3 ≤ 16 * n₃ / a ^ 2) ∧
          (0 ≤ y 2 + y 3 ∧ y 2 + y 3 ≤ 64 * ε / a) ∧
          (0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 256 * n₂ * n₃ / a ^ 4) := by
  obtain ⟨C, _, h₀, hh₀, H₀⟩ := exists_restartShearFastEntry_control
  refine ⟨min h₀ 1, lt_min hh₀ (by norm_num), ?_⟩
  intro h hh q hq
  obtain ⟨astar, hastar, Ha⟩ := H₀ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T y
  let Z := restartShearCurve σ n₂ n₃ ρ
  let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
  let p := restartSectionRadialState h T Z
  obtain ⟨ha1, hasmall, hT, hrad, hdom, _, hneg, Hcurve, hnpos, hnexp, hshear, hc, hv, _, hw⟩ :=
    Ha a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  change 0 < x 2 at hnpos
  change x 2 ≤ h * a ^ q at hnexp
  change 3 * a / 4 ≤ σ * x 1 ∧ σ * x 1 ≤ 9 * a / 4 at hshear
  have hnsq : p.1 ≤ a ^ 2 := hnexp.trans (by
    have HP : a ^ q ≤ a ^ 2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hq.le
    exact (mul_le_mul_of_nonneg_left HP hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg a) (hh.2.trans (min_le_right _ _))))
  have Hweak (i : Fin 2) : 0 ≤ p.2 i.succ ∧ p.2 i.succ ≤ a / 16 := by
    have hZi : 0 ≤ Z i.succ ∧ Z i.succ ≤ 2 * ε * a := by fin_cases i; exact h₂; exact h₃
    constructor
    · exact (div_nonneg hZi.1 (by norm_num)).trans (hw i).1
    · have H := (hw i).2.1.trans (mul_le_mul_of_nonneg_left hZi.2 (by norm_num))
      nlinarith only [H, mul_le_mul_of_nonneg_right hε.2 ha.1.le]
  have hpsmall : ‖p‖ ≤ 8 * a := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos (show 0 < p.1 from hnpos)]
    refine ⟨hnsq.trans ?_, hc⟩
    nlinarith only [ha.1, ha1]
  obtain ⟨hd, Hlo, Hhi⟩ := restartProjectionHeight_shear_bounds
    ⟨ha.1, by linarith only [hasmall]⟩ hσ hshear ⟨hnpos.le, hnsq⟩ (Hweak 0) (Hweak 1)
  have Hgerm := (eventually_restartSectionProjectionHeight_eq hrad hT (by linarith only [hneg])).comp_tendsto
    (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).continuousAt
  change (fun t => restartProjectionHeight (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))) =ᶠ[𝓝 ρ]
    restartFastShearHeight h T σ n₂ n₃ at Hgerm
  have HD := restartProjectionHeight_derivative_bound Hcurve hd hpsmall hv
  have Hactual := HD.1.hasDerivAt.congr_of_eventuallyEq Hgerm.symm
  change a ^ 2 / 4 ≤ restartProjectionHeight p at Hlo
  change restartProjectionHeight p ≤ 6 * a ^ 2 at Hhi
  have heq : restartProjectionHeight p = 1 + x 0 := Hgerm.eq_of_nhds
  rw [heq] at Hlo Hhi
  have hA : 0 < 1 + x 0 := (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le Hlo
  have Hchart := ((contDiffAt_restartSectionChart hrad 1).differentiableAt (by norm_num)).comp ρ
    (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).differentiableAt
  have HX := (hasFDerivAt_normalizedMaxCurve_initial hdom).differentiableAt.comp ρ Hchart
  have HY := ((contDiffAt_toProjectiveState 1 hA.ne').differentiableAt (by norm_num)).comp ρ HX
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have Hcoord (u u₀ : ℝ) (hu₀ : 0 ≤ u₀) (hu : u₀ / 2 ≤ u ∧ u ≤ 2 * u₀) :
      u₀ / (12 * a ^ 2) ≤ Real.sqrt 3 * u / (1 + x 0) ∧
        Real.sqrt 3 * u / (1 + x 0) ≤ 16 * u₀ / a ^ 2 := by
    have hu0 : 0 ≤ u := (div_nonneg hu₀ (by norm_num)).trans hu.1
    constructor
    · calc
        _ = (u₀ / 2) / (6 * a ^ 2) := by ring
        _ ≤ _ := div_le_div₀ (by positivity)
          (hu.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hu0])) hA Hhi
    · calc
        _ ≤ (4 * u₀) / (a ^ 2 / 4) := div_le_div₀ (by positivity)
          (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hu0, hu.2]) (by positivity [ha.1]) Hlo
        _ = _ := by ring
  have HV := Hcoord (x 3) n₂ h₂.1 ⟨(hw 0).1, (hw 0).2.1⟩
  have HW := Hcoord (x 4) n₃ h₃.1 ⟨(hw 1).1, (hw 1).2.1⟩
  have hyV : 0 ≤ y 2 := (div_nonneg h₂.1 (by positivity)).trans HV.1
  have hyW : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans HW.1
  refine ⟨hdom, HY, Hactual.differentiableAt, Hlo, Hhi, ?_, ?_, ?_, HV, HW, ?_, ?_⟩
  · rw [Hactual.deriv]
    exact HD.2.trans (by ring_nf; rfl)
  · have heqM : σ * y 0 = Real.sqrt 3 * (σ * x 1) / (1 + x 0) := by
      change σ * (Real.sqrt 3 * x 1 / (1 + x 0)) = _
      ring
    rw [heqM]
    have hspos : 0 ≤ σ * x 1 := (by positivity [ha.1] : 0 ≤ 3 * a / 4).trans hshear.1
    constructor
    · calc
        _ = (3 * a / 4) / (6 * a ^ 2) := by field_simp; ring
        _ ≤ _ := div_le_div₀ (by positivity [ha.1])
          (hshear.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt1 hspos])) hA Hhi
    · calc
        _ ≤ (2 * (9 * a / 4)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [ha.1])
          (by nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hspos, hshear.2]) (by positivity [ha.1]) Hlo
        _ = _ := by field_simp; ring
  · refine ⟨div_pos (mul_pos hsqrt hnpos) hA, ?_⟩
    calc
      y 1 ≤ (2 * (h * a ^ q)) / (a ^ 2 / 4) := div_le_div₀ (by positivity [hh.1, ha.1])
        (by
          change Real.sqrt 3 * x 2 ≤ 2 * (h * a ^ q)
          nlinarith only [mul_le_mul_of_nonneg_right hsqrt2 hnpos.le, hnexp]) (by positivity [ha.1]) Hlo
      _ = _ := by rw [Real.rpow_sub ha.1, Real.rpow_two]; ring
  · refine ⟨add_nonneg hyV hyW, ?_⟩
    calc
      y 2 + y 3 ≤ 16 * n₂ / a ^ 2 + 16 * n₃ / a ^ 2 := add_le_add HV.2 HW.2
      _ ≤ 16 * (2 * ε * a) / a ^ 2 + 16 * (2 * ε * a) / a ^ 2 := by gcongr; exact h₂.2; exact h₃.2
      _ = _ := by field_simp; ring
  · refine ⟨mul_nonneg hyV hyW, ?_⟩
    calc
      y 2 * y 3 ≤ (16 * n₂ / a ^ 2) * (16 * n₃ / a ^ 2) :=
        mul_le_mul HV.2 HW.2 hyW (by positivity [h₂.1])
      _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearCore_geometry {a m v : ℝ} (ha : a ∈ Ioc (0 : ℝ) (1 / 128))
    (hm : 1 / (8 * a) ≤ m ∧ m ≤ 18 / a) (hv : 0 ≤ v ∧ v ≤ 1 / a) :
    1 < m ∧ 6 ≤ coreRadius m v ∧ 1 / (16 * a) ≤ coreRadius m v ∧
      coreRadius m v ≤ 32 / a ∧
      (1 ≤ v → coreAngle m v ∈ Icc (-Real.arcosh (coreRadius m v)) 0) := by
  have hapos := ha.1
  have hm1 : 1 < m := lt_of_lt_of_le
    ((lt_div_iff₀ (by positivity : 0 < 8 * a)).mpr (by linarith only [ha.2])) hm.1
  have hgap : 1 / (16 * a) ≤ m - 1 := by
    have H : (1 : ℝ) ≤ 1 / (16 * a) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith only [ha.2])
    have heq : 1 / (8 * a) = 2 * (1 / (16 * a)) := by ring
    rw [heq] at hm
    linarith only [hm.1, H]
  have hklo := hgap.trans ((le_abs_self _).trans (coreRadius_component_bounds m v).1)
  have hk6 : 6 ≤ coreRadius m v := le_trans
    ((le_div_iff₀ (by positivity : 0 < 16 * a)).mpr (by linarith only [ha.2])) hklo
  have hkadd : coreRadius m v ≤ m + v := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by linarith only [hm1, hv.1])).mp
    change coreRadius m v ^ 2 ≤ (m + v) ^ 2
    rw [coreRadius_sq]
    unfold coreEnergy
    nlinarith only [hm1, mul_nonneg (by linarith only [hm1] : 0 ≤ m) hv.1]
  have hkhi : coreRadius m v ≤ 32 / a := hkadd.trans (by
    have H := add_le_add hm.2 hv.2
    have H19 : (18 : ℝ) / a + 1 / a ≤ 32 / a := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) ha.1.le
    exact H.trans H19)
  refine ⟨hm1, hk6, hklo, hkhi, ?_⟩
  intro hv1
  refine ⟨(abs_le.mp (coreAngle_abs_le_arcosh hv1)).1, ?_⟩
  change Real.arsinh ((1 - m) / v) ≤ 0
  have H : (1 - m) / v ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith only [hm1]) hv.1
  simpa only [Real.arsinh_zero] using Real.arsinh_le_arsinh.mpr H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartFastShearCore_geometry :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) →
        (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := q / 2 * Real.log (1 / a)
          let y := restartFastShearProjectiveEntry h T 1 n₂ n₃ ρ
          let k := restartFastShearCoreRadius h T 1 n₂ n₃ ρ
          let z := restartFastShearCoreAngle h T 1 n₂ n₃ ρ
          0 ≤ T ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
          T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
          0 < restartFastShearHeight h T 1 n₂ n₃ ρ ∧
          DifferentiableAt ℝ (restartFastShearProjectiveEntry h T 1 n₂ n₃) ρ ∧
          1 < y 0 ∧ 6 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧
          (1 ≤ y 2 → z ∈ Icc (-Real.arcosh k) 0) := by
  obtain ⟨hP, hhP, HP⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hP (1 / 16), lt_min hhP (by norm_num), ?_⟩
  intro h hh q hq
  obtain ⟨aP, haP, HaP⟩ := HP h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  refine ⟨min aP (1 / 128), lt_min haP (by norm_num), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ ρ hρ T y k z
  have ha128 : a ≤ 1 / 128 := ha.2.trans (min_le_right _ _)
  obtain ⟨Hdom, HY, _, HA, _, _, HM, _, HV, HW, HS, _⟩ :=
    HaP a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ ρ hρ
  change 1 / (8 * a) ≤ 1 * y 0 ∧ 1 * y 0 ≤ 18 / a at HM
  simp only [one_mul] at HM
  have hv0 : 0 ≤ y 2 := (div_nonneg h₂.1 (by positivity)).trans HV.1
  have hw0 : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans HW.1
  have hvhi : y 2 ≤ 1 / a := by
    have H : y 2 + y 3 ≤ 64 * ε / a := HS.2
    have HB : 64 * ε / a ≤ 1 / a := div_le_div_of_nonneg_right
      (by linarith only [hε.2]) ha.1.le
    linarith only [H, HB, hw0]
  have HG := shearCore_geometry ⟨ha.1, ha128⟩ HM ⟨hv0, hvhi⟩
  have hsmall : ‖restartShearCurve 1 n₂ n₃ ρ‖ ≤ 1 / 16 :=
    (restartShearCurve_annulus ha.1 hρ (by norm_num) hε h₂ h₃).1.trans
      (by linarith only [ha128])
  have hrad := restartSectionRadicand_pos_of_small
    (by rw [abs_of_pos hh.1]; exact hh.2.trans (min_le_right _ _)) hsmall
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq])
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by linarith only [ha128])))
  exact ⟨hT, hrad, Hdom, (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le HA, HY, HG⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.restartShearReturnParameters_eventuallyEq {h s n₂ n₃ ρ k : ℝ}
    (hY : ContinuousAt (restartFastShearProjectiveEntry h s 1 n₂ n₃) ρ)
    (hk : 6 ≤ k) (hy : coreRegion k (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ))
    (hR : coreRadius (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 0)
      (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2) = k)
    (hV : 1 < restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 ∨
      (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 = 1 ∧ 1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 0)) :
    restartShearReturnParameters h s n₂ n₃ =ᶠ[𝓝 ρ] fun a =>
      let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ a
      let out := projectiveOriginalFlow y 0 (partialCoreDownwardReturnTime y)
      coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3] := by
  filter_upwards [hY.tendsto.eventually
    (partialCoreDownwardReturn_connectionParameters_eventuallyEq hk hy hR hV)] with a ha
  exact ha.symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartShearPartialCore_entry :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 64) → (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let y := restartFastShearProjectiveEntry h T 1 n₂ n₃ ρ
            let k := restartFastShearCoreRadius h T 1 n₂ n₃ ρ
            let z := restartFastShearCoreAngle h T 1 n₂ n₃ ρ
            0 ≤ T ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
            T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            0 < restartFastShearHeight h T 1 n₂ n₃ ρ ∧
            1 < y 0 ∧ 6 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧
            toCoreAngleState y 0 = k ∧ 0 < y 1 ∧ 0 ≤ y 2 * y 3 ∧
            y 1 + y 2 * y 3 ≤ η / k ∧
            (1 ≤ y 2 → z ∈ Icc (-Real.arcosh k) 0 ∧
              fromCoreAngleState z (toCoreAngleState y) = y ∧ coreRegion k y ∧
              (1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0))) := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartFastShearCore_geometry
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hG hV, lt_min hhG hhV, ?_⟩
  intro h hh q P hq hP η hη
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨aG, haG, HaG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq2
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q hq2
  obtain ⟨aB, haB, HaB⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_core_budget (h := h) (M := 1) hq hP hη.1)
  refine ⟨min aG (min aV aB), lt_min haG (lt_min haV haB), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ T y k z
  have hapos := ha.1
  obtain ⟨hT, hrad, hdom, hA, _, hm, hk, hklo, hkhi, hz⟩ :=
    HaG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ ρ hρ
  obtain ⟨_, _, _, _, _, _, _, hu, _, _, _, hp⟩ :=
    HaV a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ ρ hρ
  change 6 ≤ k at hk
  change k ≤ 32 / a at hkhi
  change 0 < y 1 ∧ y 1 ≤ 8 * h * a ^ (q - 2) at hu
  change 0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 256 * n₂ * n₃ / a ^ 4 at hp
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk
  have hn₂ : n₂ ≤ a := by
    have H := mul_le_mul_of_nonneg_right hε.2 ha.1.le
    nlinarith only [h₂.2, H, ha.1]
  have HU : 0 ≤ y 1 ∧ y 1 ≤ 32 * h * a ^ (q - 2) := ⟨hu.1.le, hu.2.trans (by
    nlinarith only [mul_nonneg hh.1.le (Real.rpow_nonneg ha.1.le (q - 2))])⟩
  have HP : 0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 2048 * 1 * n₃ / a ^ 3 := by
    refine ⟨hp.1, hp.2.trans ?_⟩
    calc
      _ ≤ 256 * a * n₃ / a ^ 4 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hn₂]) h₃.1) (by positivity)
      _ = 256 * n₃ / a ^ 3 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) h₃.1) (by positivity)
  have HB := HaB ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hbudget : y 1 + y 2 * y 3 ≤ η / k :=
    restart_core_amplitude_budget ha.1 (by norm_num : (0 : ℝ) ≤ 1) hk0 hkhi HU HP h₃P HB
  refine ⟨hT, hrad, hdom, hA, hm, hk, hklo, hkhi, rfl, hu.1, hp.1, Hbudget, ?_⟩
  intro hv
  refine ⟨hz hv, fromCoreAngleState_toCoreAngleState (zero_lt_one.trans_le hv),
    partialCoreEntry_region hk hv hu.1.le hp.1 hη.2 Hbudget, ?_⟩
  rcases eq_or_lt_of_le hv with heq | hlt
  · exact Or.inr ⟨heq.symm, hm.le⟩
  · exact Or.inl hlt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartFastShearProjectiveEntry_flow {h s σ n₂ n₃ ρ t : ℝ}
    (hrad : 0 ≤ restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ))
    (hs : 0 ≤ s) (hA : 0 < restartFastShearHeight h s σ n₂ n₃ ρ) (ht : 0 ≤ t) :
    projectiveOriginalFlow (restartFastShearProjectiveEntry h s σ n₂ n₃ ρ) 0 t =
      toProjectiveState (normalizedMaxCurve (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 (s + t)) := by
  have hc := restartSectionChart_constraint hrad
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hbase := fromProjectiveState_toProjectiveState hA.ne'
    ((normalizedMaxCurve_constraint hdom).trans hc)
  have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hdom)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hs))
  simp only [zero_add] at H
  change toProjectiveState (normalizedMaxCurve
    (fromProjectiveState (toProjectiveState (normalizedMaxCurve _ 0 s))) 0 t) = _
  rw [hbase, H, add_comm t s]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearPartialCore_downward_cone :
    ∃ hstar > (0 : ℝ), ∃ K ≥ (1 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let k := restartFastShearCoreRadius h s 1 n₂ n₃
            let U := fun r => Y r 1
            let p := fun r => Y r 2 * Y r 3
            let τ := partialCoreDownwardReturnTime
            let f := fun r => partialCoreDownwardReturnState (Y r) 0
            let fU := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r)) 1
            let fP := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r)) 3
            let A := (200 * coreVariationBound + 2) * K ^ 2
            let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
            1 ≤ Y ρ 2 →
            s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            IsLeast {t | s < t ∧ toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 t) 2 = 1}
              (s + τ (Y ρ)) ∧
            partialCoreDownwardReturnState (Y ρ) = toCoreAngleState (toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 (s + τ (Y ρ)))) ∧
            DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ fU ρ ∧ DifferentiableAt ℝ fP ρ ∧
            1 / (8192 * a ^ 2) ≤ -deriv f ρ ∧ |deriv f ρ| ≤ (K + 1 / 8192) / a ^ 2 ∧
            0 ≤ fU ρ ∧ 0 ≤ fP ρ ∧ fU ρ ≤ U ρ * Real.exp (-k ρ / 12) ∧ fP ρ ≤ p ρ ∧
            |deriv fU ρ| ≤ (8192 * (K + 24 * A) * Real.sqrt (U ρ)) * Real.sqrt (fU ρ) * |deriv f ρ| ∧
            |deriv fP ρ| ≤ (8192 * K * (1 + B) * a * Real.sqrt (p ρ)) * Real.sqrt (fP ρ) * |deriv f ρ| ∧
            (U ρ = 0 → fU ρ = 0 ∧ deriv fU ρ = 0) ∧
            (p ρ = 0 → fP ρ = 0 ∧ deriv fP ρ = 0) := by
  obtain ⟨hstar, hhstar, K, hK, H⟩ := exists_restartShearPartialCore_radial_data
  have hK0 : 0 < K := by linarith only [hK]
  let C₀ := 4096 * coreVariationBound
  have hC₀ : 0 < C₀ := mul_pos (by norm_num) (Real.exp_pos _)
  refine ⟨hstar, hhstar, K, hK, ?_⟩
  intro h hh q P hq hP
  obtain ⟨a₀, ha₀, Ha⟩ := H h hh q P hq hP
  refine ⟨min a₀ (1 / (8 * C₀ * K ^ 3 * 4096)), lt_min ha₀ (by positivity), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k U p τ f fU fP A B hv
  obtain ⟨ha1, hs, hrad, hdom, hA, hY, hk, hy, hvcase, hz, hsum, hklo, hkhi, hdk, hdklo, hdU, hdp, hdz⟩ :=
    Ha a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  have hk0 : 0 < k ρ := by linarith only [hk]
  have hki : 1 / k ρ ≤ K * a := by
    apply (div_le_iff₀ hk0).mpr
    have Hb := (div_le_iff₀ (mul_pos hK0 ha.1)).mp hklo
    nlinarith only [Hb]
  have hsum' : U ρ + a * p ρ ≤ K * a := by
    have Hp := mul_le_mul_of_nonneg_right ha1 hy.2.2.2.1
    have Hsum := hsum.trans hki
    change U ρ + p ρ ≤ K * a at Hsum
    nlinarith only [Hp, Hsum]
  have hsmall : 4 * C₀ * K ^ 2 * (U ρ + a * p ρ) ≤ 1 / (2 * 4096) := by
    apply le_trans (mul_le_mul_of_nonneg_left hsum' (by positivity))
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 * 4096)).mpr
    have Hb := (le_div_iff₀ (by positivity : 0 < 8 * C₀ * K ^ 3 * 4096)).mp
      (ha.2.trans (min_le_right _ _))
    nlinarith only [Hb]
  have hkZ : 2 * Real.cosh 0 ≤ k ρ := by rw [Real.cosh_zero]; linarith only [hk]
  have HC := partialCoreDownwardReturn_radial_cone ⟨ha.1, ha1⟩ hK (by norm_num : (0 : ℝ) < 4096)
    (le_refl (0 : ℝ)) hY hk hy hvcase hkZ hz hklo hkhi hdk hdklo hdU hdp hdz hsmall
  have hfirst := (partialCoreDownwardReturn_regular hk hy rfl hvcase).1
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  refine ⟨hdom, ?_, ?_, ?_⟩
  · refine ⟨⟨by linarith only [hfirst.1.1], ?_⟩, ?_⟩
    · rw [← Hflow _ hfirst.1.1.le]
      exact hfirst.1.2
    · intro t ht
      have hsub : 0 < t - s := sub_pos.mpr ht.1
      have HF := Hflow (t - s) hsub.le
      rw [add_sub_cancel] at HF
      have Hleast := hfirst.2 ⟨hsub, by rw [HF]; exact ht.2⟩
      linarith only [Hleast]
  · change toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 (τ (Y ρ))) = _
    rw [Hflow _ hfirst.1.1.le]
  · simp only [show (2 : ℝ) * 4096 = 8192 by norm_num] at HC
    exact HC

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearPartialCore_downward_connection :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
              let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
              let k := restartFastShearCoreRadius h s 1 n₂ n₃ ρ
              let T := partialCoreDownwardReturnTime y
              let out := projectiveOriginalFlow y 0 T
              let p := coreExitConnectionParameters (partialCoreDownwardReturnState y)
              1 ≤ y 2 →
              0 < T ∧ IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} (s + T) ∧
              out = connectionEntry (p 0) (p 1) (p 2) ∧
              (4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k) ∧
              (0 < p 1 ∧ p 1 ≤ η / p 0) ∧ (0 < p 2 ∧ p 2 ≤ η) ∧
              p 1 ≤ y 1 * Real.exp (-k / 12) ∧ p 2 ≤ y 2 * y 3 ∧
              phaseNorm (p 0 + 1) 1 = coreRadius (out 0) (out 2) ∧
              connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
              ContDiffAt ℝ 2 connectionReturnState p ∧
              connectionReturnState p = toProjectiveState
                (normalizedMaxCurve x 0 (s + T + connectionReturnTime p)) ∧
              let Q := fun z => coreExitConnectionParameters (partialCoreDownwardReturnState z)
              ContDiffAt ℝ 2 Q y ∧
                ContDiffAt ℝ 2 (fun z => partialCoreDownwardReturnTime z + connectionReturnTime (Q z)) y ∧
                ContDiffAt ℝ 2 (fun z => connectionReturnState (Q z)) y := by
  obtain ⟨hstar, hhstar, H⟩ := exists_restartShearPartialCore_entry
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP η hη
  obtain ⟨astar, hastar, Ha⟩ := H h hh q P hq hP η hη
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s x y k T out p hv
  obtain ⟨hs, hrad, _, hA, _, hk, _, _, hR, hu0, hp0, hsum, Hentry⟩ :=
    Ha a ha ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  obtain ⟨hz, _, hy, hvcase⟩ := Hentry hv
  have hc : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have Hsign := normalizedMaxCurve_wall_sign hc hs (2 : Fin 3)
  have hnpos : 0 < normalizedMaxCurve x 0 s 4 := by
    have Hnonneg : 0 ≤ wallValue 2 (normalizedMaxCurve x 0 s) := Hsign.2.mpr h₃.1.le
    have Hne : wallValue 2 (normalizedMaxCurve x 0 s) ≠ 0 := fun hzero => h₃.1.ne' (Hsign.1.mp hzero)
    exact lt_of_le_of_ne Hnonneg (Ne.symm Hne)
  have hwpos : 0 < y 3 := div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hnpos) hA
  have hp : 0 < y 2 * y 3 := mul_pos (zero_lt_one.trans_le hv) hwpos
  have huη : y 1 ≤ η / k := (le_add_of_nonneg_right hp0).trans hsum
  have hpη : y 2 * y 3 ≤ η / k := (le_add_of_nonneg_left hu0.le).trans hsum
  have hkZ : 2 * Real.cosh 0 ≤ k := by rw [Real.cosh_zero]; linarith only [hk]
  obtain ⟨hentry, hμ, hu, hw, hdecU, hdecP, hphase, _, hvalid, hct, hcs, Hconn⟩ :=
    partialCoreDownwardReturn_connection_domain hk hy hR hvcase (le_refl (0 : ℝ)) hkZ hz.2 hη
      ⟨hu0, huη⟩ ⟨hp, hpη⟩
  have Hreg := partialCoreDownwardConnection_regular hk hy hR hvcase (le_refl (0 : ℝ)) hkZ hz.2 hη
    ⟨hu0, huη⟩ ⟨hp, hpη⟩
  have hfirst := (partialCoreDownwardReturn_regular hk hy hR hvcase).1
  have hT : 0 < T := hfirst.1.1
  have htc : 0 < connectionReturnTime p := hvalid.1.1.1
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  have Hfast := Hflow (T + connectionReturnTime p) (add_nonneg hT.le htc.le)
  refine ⟨hT, ?_, hentry, hμ, hu, hw, hdecU, hdecP, hphase, hvalid, hct, hcs, ?_, Hreg⟩
  · refine ⟨⟨by linarith only [hT], ?_⟩, ?_⟩
    · rw [← Hflow T hT.le]
      exact hfirst.1.2
    · intro t ht
      have hsub : 0 < t - s := sub_pos.mpr ht.1
      have HF := Hflow (t - s) hsub.le
      rw [add_sub_cancel] at HF
      have Hleast := hfirst.2 ⟨hsub, by rw [HF]; exact ht.2⟩
      linarith only [Hleast]
  · exact (Hconn.trans Hfast).trans (by rw [add_assoc])

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartShearPartialCore_downward_cone_decay :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∃ C > (0 : ℝ),
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ δ > (0 : ℝ), ∃ astar > (0 : ℝ),
        ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let τ := partialCoreDownwardReturnTime
            let f := fun r => partialCoreDownwardReturnState (Y r) 0
            let fU := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r)) 1
            let fP := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r)) 3
            let E := a ^ ((q - 2) / 2) + Real.sqrt (n₃ / a)
            1 ≤ Y ρ 2 →
            IsLeast {t | s < t ∧ toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 t) 2 = 1}
              (s + τ (Y ρ)) ∧
            DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ fU ρ ∧ DifferentiableAt ℝ fP ρ ∧
            deriv f ρ < 0 ∧ 0 ≤ fU ρ ∧ 0 ≤ fP ρ ∧ C * E ≤ δ ∧
            |deriv fU ρ| ≤ C * E * Real.sqrt (fU ρ) * |deriv f ρ| ∧
            |deriv fP ρ| ≤ C * E * Real.sqrt (fP ρ) * |deriv f ρ| ∧
            |deriv fU ρ| ≤ δ * Real.sqrt (fU ρ) * |deriv f ρ| ∧
            |deriv fP ρ| ≤ δ * Real.sqrt (fP ρ) * |deriv f ρ| ∧
            (0 < fU ρ → 0 < fP ρ →
              |deriv fU ρ| / (Real.sqrt (fU ρ) * |deriv f ρ|) +
                |deriv fP ρ| / (Real.sqrt (fP ρ) * |deriv f ρ|) ≤ C * E) ∧
            (n₃ = 0 → fP ρ = 0 ∧ deriv fP ρ = 0) := by
  obtain ⟨hC, hhC, K, hK, HC⟩ := exists_restartShearPartialCore_downward_cone
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hC hV, lt_min hhC hhV, ?_⟩
  intro h hh
  let A := (200 * coreVariationBound + 2) * K ^ 2
  let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
  let CU := 8192 * (K + 24 * A)
  let CP := 8192 * K * (1 + B)
  let C := 1 + CU * Real.sqrt (32 * h) + CP * Real.sqrt (2048 * 1)
  have hK0 : 0 < K := by linarith only [hK]
  have hA : 0 ≤ A := by dsimp only [A, coreVariationBound]; positivity
  have hB : 0 ≤ B := by dsimp only [B, coreVariationBound]; positivity
  have hCU : 0 ≤ CU := by dsimp only [CU]; positivity
  have hCP : 0 ≤ CP := by dsimp only [CP]; positivity
  have hCpos : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro q P hq hP δ hδ
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q (by linarith only [hq])
  obtain ⟨aB, haB, HaB⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_core_cone_budget hCpos.le (by linarith only [hq]) (by linarith only [hP]) hδ)
  refine ⟨min aC (min aV aB), lt_min haC (lt_min haV haB), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y τ f fU fP E hv
  have haV' := ha.2.trans (min_le_right _ _)
  obtain ⟨_, _, _, _, _, _, _, hu, _, _, _, hp⟩ :=
    HaV a ⟨ha.1, haV'.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ ρ hρ
  change 0 < Y ρ 1 ∧ Y ρ 1 ≤ 8 * h * a ^ (q - 2) at hu
  change 0 ≤ Y ρ 2 * Y ρ 3 ∧ Y ρ 2 * Y ρ 3 ≤ 256 * n₂ * n₃ / a ^ 4 at hp
  have hn₂ : n₂ ≤ a := by
    have H := mul_le_mul_of_nonneg_right hε.2 ha.1.le
    nlinarith only [h₂.2, H, ha.1]
  have HUamp : 0 ≤ Y ρ 1 ∧ Y ρ 1 ≤ 32 * h * a ^ (q - 2) := ⟨hu.1.le, hu.2.trans (by
    nlinarith only [mul_nonneg hh.1.le (Real.rpow_nonneg ha.1.le (q - 2))])⟩
  have HPamp : 0 ≤ Y ρ 2 * Y ρ 3 ∧ Y ρ 2 * Y ρ 3 ≤ 2048 * 1 * n₃ / a ^ 3 := by
    refine ⟨hp.1, hp.2.trans ?_⟩
    calc
      _ ≤ 256 * a * n₃ / a ^ 4 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hn₂]) h₃.1) (by positivity)
      _ = 256 * n₃ / a ^ 3 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) h₃.1) (by positivity [ha.1])
  have HB : CU * Real.sqrt (Y ρ 1) + CP * a * Real.sqrt (Y ρ 2 * Y ρ 3) ≤ C * E :=
    restart_core_sqrt_budget ha.1 hh.1.le (by norm_num : (0 : ℝ) ≤ 1) h₃.1 HUamp HPamp hCU hCP
      (by dsimp only [C]; linarith)
  have Hδ : C * E ≤ δ := HaB ⟨ha.1, haV'.trans (min_le_right _ _)⟩ n₃ ⟨h₃.1, h₃P⟩
  have HU : CU * Real.sqrt (Y ρ 1) ≤ C * E := le_trans
    (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hCP ha.1.le) (Real.sqrt_nonneg _))) HB
  have HP : CP * a * Real.sqrt (Y ρ 2 * Y ρ 3) ≤ C * E :=
    le_trans (le_add_of_nonneg_left (by positivity)) HB
  obtain ⟨_, horig, _, hf, hfu, hfp, hslope, _, hu0, hp0, _, _, hdu, hdp, _, hzeroP⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  have hpos : 0 < 1 / (8192 * a ^ 2) := by positivity [ha.1]
  have hspeed := hpos.trans_le (hslope.trans (neg_le_abs _))
  have hdu' := hdu.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right HU (Real.sqrt_nonneg _)) (abs_nonneg _))
  have hdp' := hdp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right HP (Real.sqrt_nonneg _)) (abs_nonneg _))
  refine ⟨horig, hf, hfu, hfp, by linarith only [hslope, hpos], hu0, hp0, Hδ, hdu', hdp', ?_, ?_, ?_, ?_⟩
  · exact hdu'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right Hδ (Real.sqrt_nonneg _)) (abs_nonneg _))
  · exact hdp'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right Hδ (Real.sqrt_nonneg _)) (abs_nonneg _))
  · intro hfu0 hfp0
    have H₁ : |deriv fU ρ| / (Real.sqrt (fU ρ) * |deriv f ρ|) ≤ CU * Real.sqrt (Y ρ 1) :=
      (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hfu0) hspeed)).mpr (hdu.trans_eq (by ring))
    have H₂ : |deriv fP ρ| / (Real.sqrt (fP ρ) * |deriv f ρ|) ≤ CP * a * Real.sqrt (Y ρ 2 * Y ρ 3) :=
      (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hfp0) hspeed)).mpr (hdp.trans_eq (by ring))
    exact (add_le_add H₁ H₂).trans HB
  · intro hz
    have hpzero : Y ρ 2 * Y ρ 3 = 0 := by
      simp only [hz, mul_zero, zero_div] at HPamp
      exact le_antisymm HPamp.2 HPamp.1
    exact hzeroP hpzero

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_restartFastShearProjectiveEntry_joint {h s σ n₂ n₃ ρ : ℝ}
    (hZ : 0 < restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ))
    (hs : s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0)
    (hA : restartFastShearHeight h s σ n₂ n₃ ρ ≠ 0) :
    ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s σ p.1.1 p.1.2 p.2)
      ((n₂, n₃), ρ) := by
  have hc : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearCurve σ p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [restartShearCurve] <;> fun_prop
  have hchart := (contDiffAt_restartSectionChart hZ 2).comp ((n₂, n₃), ρ) hc
  have hflow := (contDiffAt_normalizedMaxCurve_two hs).comp ((n₂, n₃), ρ)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (hchart.prodMk (contDiffAt_const (c := s)))
  exact (contDiffAt_toProjectiveState 2 hA).comp ((n₂, n₃), ρ) hflow

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearReturn_joint_regular :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 →
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s 1 p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnState h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnTime h s p.1.1 p.1.2 p.2) ((n₂, n₃), ρ) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_entry
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearPartialCore_downward_connection
  refine ⟨min hE hC, lt_min hhE hhC, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min aE aC, lt_min haE haC, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s hv
  obtain ⟨_, hrad, hdom, hA, _, hk, _, _, hR, _, _, _, Hentry⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  obtain ⟨_, _, hy, hvcase⟩ := Hentry hv
  obtain ⟨_, _, _, hμ, hu, hw, _, _, _, _, hct, _, _, hcp, _⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let base : (ℝ × ℝ) × ℝ := ((n₂, n₃), ρ)
  let Y := fun p : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s 1 p.1.1 p.1.2 p.2
  have hcY : ContDiffAt ℝ 2 Y base := contDiffAt_restartFastShearProjectiveEntry_joint hrad hdom hA.ne'
  have Hcore := partialCoreDownwardReturn_regular hk hy hR hvcase
  have hcP : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s p.1.1 p.1.2 p.2) base :=
    ContDiffAt.comp (g := fun z => coreExitConnectionParameters (partialCoreDownwardReturnState z))
      (f := Y) base hcp hcY
  have hcG : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnState h s p.1.1 p.1.2 p.2) base :=
    ContDiffAt.comp (g := connectionReturnPhysicalState) base
      (contDiffAt_connectionReturnPhysicalState hμ.1 ⟨hu.1.le, hu.2⟩ hw) hcP
  have hg0 : restartShearReturnState h s n₂ n₃ ρ 0 ≠ 0 := by
    change phaseNorm (-connectionReturnState (restartShearReturnParameters h s n₂ n₃ ρ) 0 - 1) 1 ≠ 0
    exact ne_of_gt (by unfold phaseNorm; positivity)
  have hcphase : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s p.1.1 p.1.2 p.2) base :=
    contDiffAt_const.div (contDiffAt_pi.mp hcG 0) hg0
  have hctime : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartShearReturnTime h s p.1.1 p.1.2 p.2) base :=
    (contDiffAt_const.add (Hcore.2.1.comp base hcY)).add
      (ContDiffAt.comp (g := connectionReturnTime) base hct hcP)
  exact ⟨hcY, hcP, hcG, hcphase, hctime⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearReturn_regular :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 →
            ContDiffAt ℝ 2 (restartFastShearProjectiveEntry h s 1 n₂ n₃) ρ ∧
            ContDiffAt ℝ 2 (restartShearReturnParameters h s n₂ n₃) ρ ∧
            ContDiffAt ℝ 2 (restartShearReturnState h s n₂ n₃) ρ ∧
            ContDiffAt ℝ 2 (restartShearReturnPhase h s n₂ n₃) ρ ∧
            ContDiffAt ℝ 2 (restartShearReturnTime h s n₂ n₃) ρ := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartShearReturn_joint_regular
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := HH h hh q P hq hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s hv
  obtain ⟨hY, hp, hG, hf, ht⟩ := Ha a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  have hc : ContDiffAt ℝ 2 (fun r : ℝ => ((n₂, n₃), r)) ρ := by fun_prop
  exact ⟨hY.comp ρ hc, hp.comp ρ hc, hG.comp ρ hc, hf.comp ρ hc, ht.comp ρ hc⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearConnection_radial_curve :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
            let τ := partialCoreDownwardReturnTime
            let out := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r))
            let f := fun r => coreRadius (out r 0) (out r 2)
            let p := fun r => coreExitConnectionParameters ![f r, out r 1, out r 3]
            let G := fun r => connectionReturnPhysicalState (p r)
            let g := fun r => G r 0
            1 ≤ Y ρ 2 →
            IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} (s + τ (Y ρ)) ∧
            connectionReturnValid (p ρ) ∧
            connectionReturnState (p ρ) = toProjectiveState
              (normalizedMaxCurve x 0 (s + τ (Y ρ) + connectionReturnTime (p ρ))) ∧
            DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ G ρ ∧
            (1 < f ρ ∧ 0 < g ρ) ∧ (deriv f ρ < 0 ∧ deriv g ρ < 0) ∧
            |deriv g ρ / deriv f ρ - 1| ≤ 1 / (4 * p ρ 0) ∧
            (3 / 4 ≤ deriv g ρ / deriv f ρ ∧ deriv g ρ / deriv f ρ ≤ 5 / 4) ∧
            (|deriv (fun r => G r 1) ρ| ≤ Real.sqrt (G ρ 1) * |deriv g ρ| ∧
              |deriv (fun r => G r 2) ρ| ≤ Real.sqrt (G ρ 2) * |deriv g ρ|) ∧
            DifferentiableAt ℝ (fun r => 2 / f r) ρ ∧
            DifferentiableAt ℝ (fun r => 2 / g r) ρ ∧
            (0 < deriv (fun r => 2 / f r) ρ ∧ 0 < deriv (fun r => 2 / g r) ρ) ∧
            2 / g ρ - 2 / f ρ = -2 * (g ρ - f ρ) / (f ρ * g ρ) ∧
            deriv (fun r => 2 / g r) ρ / deriv (fun r => 2 / f r) ρ =
              (f ρ / g ρ) ^ 2 * (deriv g ρ / deriv f ρ) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearPartialCore_downward_cone_decay
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_downward_connection
  obtain ⟨η, hη0, hη, hsη, hηL⟩ := exists_connection_cone_threshold
  refine ⟨min hC hE, lt_min hhC hhE, ?_⟩
  intro h hh q P hq hP
  obtain ⟨C, _, HC'⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  obtain ⟨aC, haC, HaC⟩ := HC' q P hq hP 1 (by norm_num)
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP η ⟨hη0, hη⟩
  refine ⟨min aC aE, lt_min haC haE, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y x τ out f p G g hv
  obtain ⟨horig, hf, hu, hw, hdf, _, _, _, _, _, hdu, hdw, _⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  obtain ⟨_, _, hentry, hμ, hu0, hw0, _, _, hphase, hvalid, _, _, horbit, _⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let u := fun r => out r 1
  let w := fun r => out r 3
  have houtV : out ρ 2 = 1 := congrArg (fun z : ProjectiveState => z 2) hentry
  have hZ : ![f ρ, u ρ, w ρ] = partialCoreDownwardReturnState (Y ρ) := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change out ρ 3 = out ρ 2 * out ρ 3
      rw [houtV, one_mul]
  have hp : p ρ = coreExitConnectionParameters (partialCoreDownwardReturnState (Y ρ)) :=
    congrArg coreExitConnectionParameters hZ
  rw [← hp] at hμ hu0 hw0 hphase hvalid horbit
  have hphase' : phaseNorm (p ρ 0 + 1) 1 = f ρ := hphase
  have hf1 : 1 < f ρ := by
    have Hb := phaseNorm_ge (b := 1) (show 0 ≤ p ρ 0 + 1 by linarith only [hμ.1])
    rw [hphase'] at Hb
    linarith only [hμ.1, Hb]
  have hu0' : 0 < u ρ ∧ u ρ ≤ η / p ρ 0 := hu0
  have hw0' : 0 < w ρ ∧ w ρ ≤ η := hw0
  simp only [one_mul] at hdu hdw
  have hdu' : |deriv u ρ| ≤ Real.sqrt (u ρ) * |deriv f ρ| := hdu
  have hdw' : |deriv w ρ| ≤ Real.sqrt (w ρ) * |deriv f ρ| := hdw
  obtain ⟨hG, hdg, hratio, hratioBounds, hgu, hgw⟩ := connectionReturn_coreExit_curve
    hf hu hw hf1 hdf ⟨hη0, hη⟩ hsη hηL hμ.1 hu0' hw0' hdu' hdw'
  have hg : DifferentiableAt ℝ g ρ := (hasDerivAt_pi.mp hG.hasDerivAt 0).differentiableAt
  have hg0 : 0 < g ρ := by
    change 0 < Real.sqrt ((-connectionReturnState (p ρ) 0 - 1) ^ 2 + 1 ^ 2)
    positivity
  have Hrec := reciprocal_curve_identities hf hg (ne_of_gt (lt_trans (by norm_num) hf1)) hg0.ne' (ne_of_lt hdf)
  exact ⟨horig, hvalid, horbit, hf, hG, ⟨hf1, hg0⟩, ⟨hdf, hdg⟩, hratio, hratioBounds,
    ⟨hgu, hgw⟩, Hrec.1, Hrec.2.1,
    ⟨reciprocal_curve_derivative_pos hf (ne_of_gt (lt_trans (by norm_num) hf1)) hdf,
      reciprocal_curve_derivative_pos hg hg0.ne' hdg⟩, Hrec.2.2⟩

end
end

/-- The same fixed shear restart preserves the square-root cone, with ordinary derivatives at V = 1. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let G := restartShearReturnState h s n₂ n₃
            let k := fun b => G b 0
            1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 →
            ContDiffAt ℝ 2 G ρ ∧ deriv k ρ < 0 ∧
            |deriv (fun b => G b 1) ρ| ≤ Real.sqrt (G ρ 1) * |deriv k ρ| ∧
            |deriv (fun b => G b 2) ρ| ≤ Real.sqrt (G ρ 2) * |deriv k ρ| := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearReturn_regular
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearConnection_radial_curve
  obtain ⟨hD, hhD, K, _, HD⟩ := exists_restartShearPartialCore_radial_data
  refine ⟨min hR (min hC hD), lt_min hhR (lt_min hhC hhD), ?_⟩
  intro h hh q P hq hP
  have hhCD := hh.2.trans (min_le_right _ _)
  obtain ⟨aR, haR, HaR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hhCD.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aD, haD, HaD⟩ := HD h ⟨hh.1, hhCD.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aR (min aC aD), lt_min haR (lt_min haC haD), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s G k hv
  have haCD := ha.2.trans (min_le_right _ _)
  obtain ⟨_, _, hcG, _⟩ :=
    HaR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, _, _, _, hneg, _, _, hcone, _⟩ :=
    HaC a ⟨ha.1, haCD.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, _, _, hY, hk, hy, hvcase, _⟩ :=
    HaD a ⟨ha.1, haCD.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
  let out := fun b => projectiveOriginalFlow (Y b) 0 (partialCoreDownwardReturnTime (Y b))
  let p := fun b => coreExitConnectionParameters ![coreRadius (out b 0) (out b 2), out b 1, out b 3]
  have heq := restartShearReturnParameters_eventuallyEq hY.continuousAt hk hy rfl hvcase
  have heqG : G =ᶠ[𝓝 ρ] fun b => connectionReturnPhysicalState (p b) :=
    heq.mono fun _ hb => congrArg connectionReturnPhysicalState hb
  have heqi (i : Fin 3) : (fun b => G b i) =ᶠ[𝓝 ρ] fun b => connectionReturnPhysicalState (p b) i :=
    heqG.mono fun _ hb => congrArg (fun z => z i) hb
  have hv1 : G ρ 1 = connectionReturnPhysicalState (p ρ) 1 := (heqi 1).self_of_nhds
  have hv2 : G ρ 2 = connectionReturnPhysicalState (p ρ) 2 := (heqi 2).self_of_nhds
  refine ⟨hcG, ?_, ?_, ?_⟩
  · change deriv (fun b => G b 0) ρ < 0
    rw [(heqi 0).deriv_eq]
    exact hneg.2
  · change |deriv (fun b => G b 1) ρ| ≤ Real.sqrt (G ρ 1) * |deriv (fun b => G b 0) ρ|
    rw [(heqi 1).deriv_eq, hv1, (heqi 0).deriv_eq]
    exact hcone.1
  · change |deriv (fun b => G b 2) ρ| ≤ Real.sqrt (G ρ 2) * |deriv (fun b => G b 0) ρ|
    rw [(heqi 2).deriv_eq, hv2, (heqi 0).deriv_eq]
    exact hcone.2
