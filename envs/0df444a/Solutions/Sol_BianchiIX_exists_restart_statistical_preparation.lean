-- Prove2me | solution 1 for BianchiIX.exists_restart_statistical_preparation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:55:49.030412+00:00
-- url     : https://prove2.me/submissions/cf57bdc5-7fe5-4360-9bd9-64ccd1a58c50

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_SectionRestartData
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_cone
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_deriv_middle
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_middle
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_pair_bound
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_pos
import Theorems.Thm_BianchiIX_connectionReturn_coreExit_curve
import Theorems.Thm_BianchiIX_contDiffAt_coreOriginalLogRates
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_moving_intervalIntegral_of_contDiffAt
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_contDiffAt_scalar_event_branch
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_contDiff_amplitudeCurveExtension
import Theorems.Thm_BianchiIX_continuousAt_activeWall_event_rate
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreClockProjection_growth
import Theorems.Thm_BianchiIX_eventually_activeWall_interior_first_hit
import Theorems.Thm_BianchiIX_eventually_partialCore_multiplier_formula
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_exists_normalized_partialCore_return
import Theorems.Thm_BianchiIX_exists_restartConnection_output_bounds
import Theorems.Thm_BianchiIX_exists_restartConnection_output_phase
import Theorems.Thm_BianchiIX_exists_restartFastProjectiveEntry_bounds
import Theorems.Thm_BianchiIX_exists_restartPartialCore_connection
import Theorems.Thm_BianchiIX_exists_restartPartialCore_radial_data
import Theorems.Thm_BianchiIX_exists_restartReturn_joint_regular
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_intervalRadiusInverse_control
import Theorems.Thm_BianchiIX_jointly_measurable_amplitudeCurve
import Theorems.Thm_BianchiIX_multiplier_radial_derivative
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_core_prefix_contraction
import Theorems.Thm_BianchiIX_normalized_core_residence
import Theorems.Thm_BianchiIX_normalized_core_return_downward
import Theorems.Thm_BianchiIX_normalized_core_return_isLeast
import Theorems.Thm_BianchiIX_normalized_partialCore_energy_band_improves
import Theorems.Thm_BianchiIX_partialCoreReturn_log_derivative_bounds
import Theorems.Thm_BianchiIX_partialCore_field_bounds
import Theorems.Thm_BianchiIX_partialCore_wall_arrival_radius_response
import Theorems.Thm_BianchiIX_partial_core_radial_derivative_budget
import Theorems.Thm_BianchiIX_partial_core_radial_log_bounds
import Theorems.Thm_BianchiIX_partial_core_radial_variation_budget
import Theorems.Thm_BianchiIX_partial_core_reciprocal_radial_bounds
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_sech_le_exp
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.Compact
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
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_scalar_event_branch_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Q : E × ℝ → ℝ} {x : E} {t a : ℝ}
    (hQ : ContDiffAt ℝ 2 Q (x, t))
    (hd : HasDerivAt (fun u => Q (x, u)) a t) (ha : a ≠ 0)
    {τ : E → ℝ} (hτ : τ x = t) (hcτ : ContinuousAt τ x)
    (hhit : ∀ᶠ y in 𝓝 x, Q (y, τ y) = Q (x, t)) : ContDiffAt ℝ 2 τ x :=
  contDiffAt_scalar_event_branch (by norm_num) hQ hd ha hτ hcτ hhit

end
end

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

private theorem BianchiIX.coreBootstrap_wall_bound {k u : ℝ} (hk : 6 ≤ k) (hu : u ≤ (1 / 10000) / k) :
    u ≤ 1 / 60000 := by
  have hk0 : 0 < k := by linarith
  exact hu.trans ((div_le_iff₀ hk0).mpr (by linarith))

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
open Set

private theorem BianchiIX.radiusAmplitude_data {k U : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x) (hd : ∀ x ∈ Icc a b, deriv k x < 0)
    (hU : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 U x) (hpos : ∀ x ∈ Icc a b, 0 < U x)
    (hcone : ∀ x ∈ Icc a b, |deriv U x| ≤ Real.sqrt (U x) * |deriv k x|) :
    let J := Icc (k b) (k a)
    let u := radiusAmplitude k U a b
    let du := radiusAmplitudeSlope k U a b
    (∀ x ∈ Icc a b, u (k x) = U x) ∧ (∀ x ∈ J, 0 < u x) ∧
      (∀ x ∈ J, HasDerivWithinAt u (du x) J x) ∧ ContinuousOn du J ∧
      ∀ x ∈ J, |du x| ≤ Real.sqrt (u x) := by
  intro J u du
  obtain ⟨_, _, hleft, hmaps, _, hder⟩ := intervalRadiusInverse_control hab hk hd
  let g := intervalRadiusInverse k a b
  have hgc : ContinuousOn g J := fun x hx => (hder x hx).continuousWithinAt
  have hdk : ContinuousOn (deriv k) (Icc a b) := fun x hx =>
    ((hk x hx).derivWithin (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousAt.continuousWithinAt
  have hdU : ContinuousOn (deriv U) (Icc a b) := fun x hx =>
    ((hU x hx).derivWithin (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousAt.continuousWithinAt
  refine ⟨?_, (fun x hx => hpos (g x) (hmaps hx)), ?_, ?_, ?_⟩
  · intro x hx
    exact congrArg U (hleft hx)
  · intro x hx
    simpa only [u, du, J, g, radiusAmplitude, radiusAmplitudeSlope, Function.comp_def, div_eq_mul_inv] using!
      (((hU (g x) (hmaps hx)).differentiableAt (by norm_num)).hasDerivAt.comp_hasDerivWithinAt x (hder x hx))
  · exact (hdU.comp hgc hmaps).div (hdk.comp hgc hmaps) (fun x hx => (hd (g x) (hmaps hx)).ne)
  · intro x hx
    change |deriv U (g x) / deriv k (g x)| ≤ Real.sqrt (U (g x))
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr (hd (g x) (hmaps hx)).ne)).mpr (hcone (g x) (hmaps hx))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.radiusAmplitudeExtension_pair {k U W : ℝ → ℝ} {a b B : ℝ} (hab : a < b)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x) (hd : ∀ x ∈ Icc a b, deriv k x < 0)
    (hU : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 U x) (hW : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 W x)
    (hposU : ∀ x ∈ Icc a b, 0 < U x) (hposW : ∀ x ∈ Icc a b, 0 < W x)
    (hconeU : ∀ x ∈ Icc a b, |deriv U x| ≤ Real.sqrt (U x) * |deriv k x|)
    (hconeW : ∀ x ∈ Icc a b, |deriv W x| ≤ Real.sqrt (W x) * |deriv k x|)
    (hB : ∀ x ∈ Icc a b, U x + W x ≤ B) :
    let u := radiusAmplitudeExtension k U a b
    let w := radiusAmplitudeExtension k W a b
    ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
      (∀ x ∈ Icc a b, u (k x) = U x ∧ w (k x) = W x ∧
        deriv u (k x) = deriv U x / deriv k x ∧ deriv w (k x) = deriv W x / deriv k x) ∧
      ∀ x : ℝ, 0 < u x ∧ 0 < w x ∧ u x + w x ≤ (25 / 16) * B ∧
        |deriv u x| ≤ Real.sqrt (u x) ∧ |deriv w x| ≤ Real.sqrt (w x) := by
  intro u w
  obtain ⟨hba, himage, hleft, hmaps, _, _⟩ := intervalRadiusInverse_control hab hk hd
  obtain ⟨hmatchU, hpu, hdu, hcu, hconeU'⟩ := radiusAmplitude_data hab hk hd hU hposU hconeU
  obtain ⟨hmatchW, hpw, hdw, hcw, hconeW'⟩ := radiusAmplitude_data hab hk hd hW hposW hconeW
  have hconeU1 (x : ℝ) (hx : x ∈ Icc (k b) (k a)) :
      |radiusAmplitudeSlope k U a b x| ≤ 1 * Real.sqrt (radiusAmplitude k U a b x) := by
    simpa only [one_mul] using hconeU' x hx
  have hconeW1 (x : ℝ) (hx : x ∈ Icc (k b) (k a)) :
      |radiusAmplitudeSlope k W a b x| ≤ 1 * Real.sqrt (radiusAmplitude k W a b x) := by
    simpa only [one_mul] using hconeW' x hx
  have hsum (x : ℝ) (hx : x ∈ Icc (k b) (k a)) :
      radiusAmplitude k U a b x + radiusAmplitude k W a b x ≤ B := hB _ (hmaps hx)
  refine ⟨contDiff_amplitudeCurveExtension hba hpu hdu hcu,
    contDiff_amplitudeCurveExtension hba hpw hdw hcw, ?_, ?_⟩
  · intro x hx
    have hxJ : k x ∈ Icc (k b) (k a) := by rw [← himage]; exact mem_image_of_mem k hx
    refine ⟨(amplitudeCurveExtension_middle hxJ (hpu _ hxJ).le).trans (hmatchU x hx),
      (amplitudeCurveExtension_middle hxJ (hpw _ hxJ).le).trans (hmatchW x hx), ?_, ?_⟩
    · change deriv (amplitudeCurveExtension _ _ _ _) (k x) = _
      rw [amplitudeCurveExtension_deriv_middle hba hpu hdu hxJ]
      change deriv U (intervalRadiusInverse k a b (k x)) / deriv k (intervalRadiusInverse k a b (k x)) = _
      rw [hleft hx]
    · change deriv (amplitudeCurveExtension _ _ _ _) (k x) = _
      rw [amplitudeCurveExtension_deriv_middle hba hpw hdw hxJ]
      change deriv W (intervalRadiusInverse k a b (k x)) / deriv k (intervalRadiusInverse k a b (k x)) = _
      rw [hleft hx]
  · intro x
    refine ⟨amplitudeCurveExtension_pos hba.le hpu hconeU1 le_rfl x,
      amplitudeCurveExtension_pos hba.le hpw hconeW1 le_rfl x,
      amplitudeCurveExtension_pair_bound hba.le hpu hpw hconeU1 hconeW1 le_rfl hsum x, ?_, ?_⟩
    · simpa only [u, radiusAmplitudeExtension, one_mul] using amplitudeCurveExtension_cone hba hpu hdu hconeU1 le_rfl x
    · simpa only [w, radiusAmplitudeExtension, one_mul] using amplitudeCurveExtension_cone hba hpw hdw hconeW1 le_rfl x

end
end

section
noncomputable section
open BianchiIX
open Set Function

private theorem BianchiIX.measurableSet_closedIntervalFamily {X : Type*} [MeasurableSpace X]
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet (closedIntervalFamily a b) :=
  (measurableSet_le (ha.comp measurable_fst) measurable_snd).inter
    (measurableSet_le measurable_snd (hb.comp measurable_fst))

end
end

section
noncomputable section
open BianchiIX
open Set Function

open scoped Classical in

private theorem BianchiIX.jointly_measurable_variable_radiusAmplitude_interior {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ q, a q < b q) {k U : X → ℝ → ℝ}
    (hk : Measurable (fun p : closedIntervalFamily a b => k p.val.1 p.val.2))
    (hU : Measurable (fun p : closedIntervalFamily a b => U p.val.1 p.val.2))
    (hkc : ∀ q, ContinuousOn (k q) (Icc (a q) (b q)))
    (hanti : ∀ q, StrictAntiOn (k q) (Icc (a q) (b q))) :
    Measurable (fun p : X × ℝ => if k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1) then
      radiusAmplitude (k p.1) (U p.1) (a p.1) (b p.1) p.2 else 0) := by
  classical
  let D := closedIntervalFamily a b
  let : StandardBorelSpace D := (measurableSet_closedIntervalFamily ha hb).standardBorel
  let H : D → X × ℝ := fun p => (p.val.1, k p.val.1 p.val.2)
  have hmH : Measurable H := (measurable_fst.comp measurable_subtype_coe).prodMk hk
  have hiH : Injective H := by
    rintro ⟨⟨q, x⟩, hx⟩ ⟨⟨q', y⟩, hy⟩ h
    have hq : q = q' := congrArg Prod.fst h
    subst q'
    have hxy : x = y := (hanti q).injOn hx hy (congrArg Prod.snd h)
    exact Subtype.ext (Prod.ext rfl hxy)
  have he := hmH.measurableEmbedding hiH
  let V := Function.extend H (fun p : D => U p.val.1 p.val.2) (fun _ => (0 : ℝ))
  have hmV : Measurable V := he.measurable_extend hU measurable_const
  have hma' : Measurable (fun q => (⟨(q, a q), le_rfl, (hab q).le⟩ : D)) :=
    (measurable_id.prodMk ha).subtype_mk
  have hmb' : Measurable (fun q => (⟨(q, b q), (hab q).le, le_rfl⟩ : D)) :=
    (measurable_id.prodMk hb).subtype_mk
  have hma : Measurable (fun q => k q (a q)) := hk.comp hma'
  have hmb : Measurable (fun q => k q (b q)) := hk.comp hmb'
  have hS : MeasurableSet {p : X × ℝ | k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1)} :=
    (measurableSet_lt (hmb.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (hma.comp measurable_fst))
  have hmask : Measurable (fun p : X × ℝ =>
      if k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1) then V p else 0) :=
    Measurable.ite hS hmV measurable_const
  convert! hmask using 1
  ext p
  by_cases hp : k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1)
  · have himage := (hkc p.1).image_Icc_of_antitoneOn (hab p.1).le (hanti p.1).antitoneOn
    obtain ⟨x, hx, hval⟩ : p.2 ∈ k p.1 '' Icc (a p.1) (b p.1) := by
      rw [himage]
      exact ⟨hp.1.le, hp.2.le⟩
    have hinv := (hanti p.1).injOn.leftInvOn_invFunOn hx
    have hV : V p = U p.1 x := by
      have hHp : H (⟨(p.1, x), hx⟩ : D) = p := Prod.ext rfl hval
      rw [← hHp]
      exact hiH.extend_apply _ _ _
    simp [hV, radiusAmplitude, intervalRadiusInverse, ← hval, hinv]
  · simp [hp]

end
end

section
noncomputable section
open BianchiIX
open Set Function

private theorem BianchiIX.jointly_measurable_radiusAmplitude_interior {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {a b : ℝ} (hab : a < b) {k U : X → ℝ → ℝ}
    (hk : Measurable (fun p : X × Icc a b => k p.1 p.2))
    (hU : Measurable (fun p : X × Icc a b => U p.1 p.2))
    (hkc : ∀ q, ContinuousOn (k q) (Icc a b))
    (hanti : ∀ q, StrictAntiOn (k q) (Icc a b)) :
    Measurable (fun p : X × ℝ => if k p.1 b < p.2 ∧ p.2 < k p.1 a then
      radiusAmplitude (k p.1) (U p.1) a b p.2 else 0) := by
  let T : closedIntervalFamily (fun _ : X => a) (fun _ => b) → X × Icc a b :=
    fun p => (p.val.1, ⟨p.val.2, p.property⟩)
  have hT : Measurable T := (measurable_fst.comp measurable_subtype_coe).prodMk
    (measurable_snd.comp measurable_subtype_coe).subtype_mk
  exact jointly_measurable_variable_radiusAmplitude_interior measurable_const measurable_const
    (fun _ => hab) (hk.comp hT) (hU.comp hT) hkc hanti

end
end

section
noncomputable section
open BianchiIX
open Set Function

set_option maxHeartbeats 600000 in

private theorem BianchiIX.jointly_measurable_radiusAmplitudeExtension {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {a b : ℝ} (hab : a < b) {k U : X → ℝ → ℝ}
    (hkm : Measurable (fun p : X × Icc a b => k p.1 p.2))
    (hUm : Measurable (fun p : X × Icc a b => U p.1 p.2))
    (hk : ∀ q x, x ∈ Icc a b → ContDiffAt ℝ 1 (k q) x)
    (hd : ∀ q x, x ∈ Icc a b → deriv (k q) x < 0)
    (hU : ∀ q x, x ∈ Icc a b → ContDiffAt ℝ 1 (U q) x)
    (hpos : ∀ q x, x ∈ Icc a b → 0 < U q x) :
    Measurable (fun p : X × ℝ => radiusAmplitudeExtension (k p.1) (U p.1) a b p.2) ∧
      Measurable (fun p : X × ℝ => deriv (radiusAmplitudeExtension (k p.1) (U p.1) a b) p.2) := by
  have hi (q : X) := intervalRadiusInverse_control hab (hk q) (hd q)
  have hma : Measurable (fun q => k q a) := hkm.comp
    (measurable_id.prodMk (measurable_const (a := (⟨a, le_rfl, hab.le⟩ : Icc a b))))
  have hmb : Measurable (fun q => k q b) := hkm.comp
    (measurable_id.prodMk (measurable_const (a := (⟨b, hab.le, le_rfl⟩ : Icc a b))))
  have hcont (q : X) : ContinuousOn (k q) (Icc a b) :=
    fun x hx => (hk q x hx).continuousAt.continuousWithinAt
  have hanti (q : X) : StrictAntiOn (k q) (Icc a b) :=
    strictAntiOn_of_deriv_neg (convex_Icc a b) (hcont q) (fun x hx => hd q x (interior_subset hx))
  have hm := jointly_measurable_radiusAmplitude_interior hab hkm hUm hcont hanti
  have hrootpos (q : X) (x : ℝ) (hx : x ∈ Icc (k q b) (k q a)) :
      0 < radiusAmplitude (k q) (U q) a b x := hpos q _ ((hi q).2.2.2.1 hx)
  have hrootder (q : X) (x : ℝ) (hx : x ∈ Icc (k q b) (k q a)) :
      HasDerivWithinAt (radiusAmplitude (k q) (U q) a b)
        (radiusAmplitudeSlope (k q) (U q) a b x) (Icc (k q b) (k q a)) x := by
    have H := ((hU q _ ((hi q).2.2.2.1 hx)).differentiableAt (by norm_num)).hasDerivAt.comp_hasDerivWithinAt x
      ((hi q).2.2.2.2.2 x hx)
    simpa only [radiusAmplitude, radiusAmplitudeSlope, Function.comp_def, div_eq_mul_inv] using! H
  exact jointly_measurable_amplitudeCurve
    (U := fun q => radiusAmplitude (k q) (U q) a b)
    (dU := fun q => radiusAmplitudeSlope (k q) (U q) a b)
    hmb hma (fun q => (hi q).1) hrootpos hm hrootder

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
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_activeWall_interior_first_hit_two {x : NormalizedState} {t₀ s t η : ℝ}
    (hst : s < t)
    (hreg : ∀ u ∈ Icc s t, u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (havoid : ∀ u ∈ Ico s t, projectiveActiveWall (normalizedMaxCurve x t₀ u) ≠ η)
    (hrate : normalizedEventRate projectiveActiveWall x t₀ t < 0)
    (hhit : projectiveActiveWall (normalizedMaxCurve x t₀ t) = η) :
    ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
      ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y))) x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x t₀ t) x ∧
      HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y)))
        ((fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)).comp
          (normalizedEventDifferential projectiveActiveWall x t₀ t)) x ∧
      (∀ᶠ y in 𝓝 x,
        IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain y t₀ ∧
          projectiveActiveWall (normalizedMaxCurve y t₀ u) = η} (τ y) ∧
        (∀ u ∈ Icc s (τ y), u ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ u 0) ∧
        normalizedEventRate projectiveActiveWall y t₀ (τ y) < 0) := by
  have hdom := (hreg t ⟨hst.le, le_rfl⟩).1
  have hA := ne_of_gt (hreg t ⟨hst.le, le_rfl⟩).2
  have hg := contDiffAt_projectiveActiveWall 2 hA
  obtain ⟨τ, hτ, hcτ, hdτ, hlocal, huniq, _, hdEnd⟩ := exists_normalized_event hdom
    (contDiffAt_projectiveActiveWall 1 hA) (ne_of_lt hrate)
  let F : NormalizedState × ℝ → NormalizedState := fun z => normalizedMaxCurve z.1 t₀ z.2
  let Q : NormalizedState × ℝ → ℝ := fun z => projectiveActiveWall (F z)
  have hcF : ContDiffAt ℝ 2 F (x, t) := contDiffAt_normalizedMaxCurve_two hdom
  have hcQ : ContDiffAt ℝ 2 Q (x, t) :=
    ContDiffAt.comp (g := projectiveActiveWall) (f := F) (x, t) hg hcF
  have htime : HasDerivAt (fun u => Q (x, u)) (normalizedEventRate projectiveActiveWall x t₀ t) t :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_normalizedMaxCurve hdom)
  have hτ2 := contDiffAt_scalar_event_branch_two hcQ htime (ne_of_lt hrate) hτ
    hcτ.continuousAt (hlocal.mono fun _ h => h.2)
  have hcEnd : ContDiffAt ℝ 2 (fun y => F (y, τ y)) x := by
    have H : ContDiffAt ℝ 2 F (x, τ x) := by rw [hτ]; exact hcF
    exact H.comp x (contDiffAt_id.prodMk hτ2)
  have hto : ContDiffAt ℝ 2 toProjectiveState (F (x, τ x)) := by
    rw [hτ]
    exact contDiffAt_toProjectiveState 2 hA
  have hdOut := (hto.differentiableAt (by norm_num)).hasFDerivAt.comp x hdEnd
  rw [hτ] at hdOut
  have Hfirst := eventually_activeWall_interior_first_hit hcτ.continuousAt
    (by rw [hτ]; exact hst) (by simpa only [hτ] using hreg) (by simpa only [hτ] using havoid)
    (hlocal.mono fun _ h => h.2.trans hhit)
    (by rw [hτ]; exact huniq.mono fun _ h hh => h.2.mp (hh.trans hhit.symm))
  have hgraph : Tendsto (fun y => (y, τ y)) (𝓝 x) (𝓝 (x, t)) := by
    simpa only [hτ, id_eq] using (continuousAt_id.prodMk hcτ.continuousAt).tendsto
  have Hrate := hgraph.eventually ((continuousAt_activeWall_event_rate hdom hA).eventually
    (isOpen_Iio.mem_nhds hrate))
  refine ⟨τ, hτ, hτ2,
    ContDiffAt.comp (g := toProjectiveState) (f := fun y => F (y, τ y)) x hto hcEnd, hdτ, hdOut, ?_⟩
  filter_upwards [Hfirst, Hrate] with y hy hr
  exact ⟨hy.1, hy.2, hr⟩

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
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_normalized_partialCore_firstReturn_two {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → 1 < β s 2 →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k) →
    ∃ t > s, ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
      ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y))) x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x t₀ t) x ∧
      HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y)))
        ((fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)).comp
          (normalizedEventDifferential projectiveActiveWall x t₀ t)) x ∧
      (∀ᶠ y in 𝓝 x,
        IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain y t₀ ∧
          projectiveActiveWall (normalizedMaxCurve y t₀ u) = 1} (τ y) ∧
        (∀ u ∈ Icc s (τ y), u ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ u 0) ∧
        normalizedEventRate projectiveActiveWall y t₀ (τ y) < 0) := by
  intro β hR hV hU hP
  obtain ⟨t, hst, hleast, _, _, hder, _, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk hs hA hR (Or.inl hV) hU hP
  have hk0 : 0 < k := by linarith only [hk]
  have hreg (u : ℝ) (hu : u ∈ Icc s t) :
      u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    ⟨normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1),
      lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H u hu).1⟩
  have havoid (u : ℝ) (hu : u ∈ Ico s t) : projectiveActiveWall (normalizedMaxCurve x t₀ u) ≠ 1 := by
    change β u 2 ≠ 1
    intro heq
    rcases eq_or_lt_of_le hu.1 with he | hlt
    · subst u
      exact (ne_of_gt hV) heq
    · exact (not_le_of_gt hu.2) (hleast.2 ⟨hlt, heq⟩)
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have HD := ((contDiffAt_projectiveActiveWall 1 (ne_of_gt (hreg t htm).2)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_normalizedMaxCurve (hreg t htm).1)
  change HasDerivAt (fun u => β u 2) (normalizedEventRate projectiveActiveWall x t₀ t) t at HD
  change deriv (fun u => β u 2) t ≤ -(1 + normalizedMaxCurve x t₀ t 0) * k / 2 at hder
  rw [HD.deriv] at hder
  have hrate : normalizedEventRate projectiveActiveWall x t₀ t < 0 := hder.trans_lt
    (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (hreg t htm).2) hk0) (by norm_num))
  exact ⟨t, hst, exists_activeWall_interior_first_hit_two hst hreg havoid hrate hleast.1.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.scaleCoreVariationLinear_apply (k : ℝ) (v : CoreAngleState) :
    scaleCoreVariationLinear k v = scaleCoreVariation k v := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.coreFlowMultiplier_pos (y : ProjectiveState) (t₀ a b : ℝ) (i : Fin 2) :
    0 < coreFlowMultiplier y t₀ a b i := Real.exp_pos _

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

private theorem BianchiIX.partialCore_weighted_field_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k) :
    ‖scaleCoreVariation k (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ ≤
      4 * (k ^ 2 * y 1 + (y 2 * y 3) / k) := by
  let F := coreAngleField (projectiveCoreAngle y) (toCoreAngleState y)
  let p := y 2 * y 3
  have hk0 : 0 < k := by linarith only [hk]
  have hu : 0 ≤ y 1 := hy.2.2.1.1
  have hp : 0 ≤ p := hy.2.2.2.1
  have hp1 : p ≤ 1 := (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)
  have hp2 : p ^ 2 / k ≤ p / k := div_le_div_of_nonneg_right (by nlinarith only [hp, hp1]) hk0.le
  have hku : k * y 1 ≤ k ^ 2 * y 1 := by
    have H : k ≤ k ^ 2 := by nlinarith only [hk]
    exact mul_le_mul_of_nonneg_right H hu
  obtain ⟨hR', hU, hP⟩ := partialCore_field_bounds hk hy hR
  change |F 0| ≤ 2 * (k * y 1 + p ^ 2 / k) at hR'
  change |F 1| ≤ 2 * k * y 1 at hU
  change |F 2| ≤ 4 * p / k at hP
  rw [show 4 * p / k = 4 * (p / k) by ring] at hP
  have hpdiv : 0 ≤ p / k := div_nonneg hp hk0.le
  have hkusq : 0 ≤ k ^ 2 * y 1 := mul_nonneg (sq_nonneg _) hu
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change |F 0| ≤ _
    linarith only [hR', hp2, hku, hkusq, hpdiv]
  · change |k * F 1| ≤ _
    rw [abs_mul, abs_of_pos hk0]
    nlinarith only [mul_le_mul_of_nonneg_left hU hk0.le, hkusq, hpdiv]
  · change |F 2| ≤ _
    linarith only [hP, hkusq]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_projectiveCoreLogRates {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y)
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow y t₀ t 2)
    (hDz : projectiveStateDenom (projectiveOriginalFlow y t₀ t) ≠ 0)
    (hd : let z := projectiveOriginalFlow y t₀ t
      coreClockFactor (coreRadius (z 0) (z 2)) (z 1) (z 3) ≠ 0) :
    ContDiffAt ℝ 1 (fun p : ProjectiveState × ℝ =>
      coreOriginalLogRates (projectiveOriginalFlow p.1 t₀ p.2)) (y, t) :=
  (contDiffAt_coreOriginalLogRates 1 hV hDz hd).comp (y, t) (g := coreOriginalLogRates)
    (f := fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 t₀ p.2)
    ((contDiffAt_projectiveOriginalFlow_two hD ht hA).of_le (by norm_num))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_log_partialCoreReturnMultiplier {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContDiffAt ℝ 1 τ y) (hpos : 0 ≤ τ y)
    (hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (i : Fin 2) : ContDiffAt ℝ 1 (fun z => Real.log (partialCoreReturnMultiplier τ z i)) y := by
  have hF (t : ℝ) (ht : t ∈ Icc 0 (τ y)) := contDiffAt_pi.mp
    (contDiffAt_projectiveCoreLogRates hD (hdom ht) (hA t ht)
      (zero_lt_one.trans_le (hcore t ht).2.1)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1)) i
  convert! contDiffAt_moving_intervalIntegral_of_contDiffAt hτ hpos hF using 1
  ext z
  exact log_coreFlowMultiplier _ _ _ _ _

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.contDiffAt_partialCoreReturnMultiplier {k : ℝ} {y : ProjectiveState}
    {τ : ProjectiveState → ℝ} (hk : 6 ≤ k) (hD : 0 < projectiveStateDenom y)
    (hτ : ContDiffAt ℝ 1 τ y) (hpos : 0 ≤ τ y)
    (hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0)
    (hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t))
    (i : Fin 2) : ContDiffAt ℝ 1 (fun z => partialCoreReturnMultiplier τ z i) y := by
  convert! (contDiffAt_log_partialCoreReturnMultiplier hk hD hτ hpos hdom hA hcore i).exp using 1
  ext z
  exact (Real.exp_log (coreFlowMultiplier_pos _ _ _ _ i)).symm

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_moving_start_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (v : CoreAngleState) (dz : ℝ) :
    ‖scaleCoreVariation k
      (v - dz • coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ ≤
      4 * partialCoreVariationBudget k (y 1) (y 2 * y 3) v dz := by
  have hk0 : 0 < k := by linarith only [hk]
  let N := |v 0| + k * |v 1| + |v 2|
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hv : ‖scaleCoreVariation k v‖ ≤ N := by
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    fin_cases i
    · change |v 0| ≤ N
      dsimp [N]
      linarith only [mul_nonneg hk0.le (abs_nonneg (v 1)), abs_nonneg (v 2)]
    · change |k * v 1| ≤ N
      rw [abs_mul, abs_of_pos hk0]
      dsimp [N]
      linarith only [abs_nonneg (v 0), abs_nonneg (v 2)]
    · change |v 2| ≤ N
      dsimp [N]
      linarith only [abs_nonneg (v 0), mul_nonneg hk0.le (abs_nonneg (v 1))]
  have hfield := partialCore_weighted_field_bound hk hy hR
  rw [← scaleCoreVariationLinear_apply, map_sub, map_smul]
  calc
    _ ≤ ‖scaleCoreVariationLinear k v‖ +
        ‖dz • scaleCoreVariationLinear k
          (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ := norm_sub_le _ _
    _ = ‖scaleCoreVariation k v‖ + |dz| *
        ‖scaleCoreVariation k (coreAngleField (projectiveCoreAngle y) (toCoreAngleState y))‖ := by
      rw [norm_smul, Real.norm_eq_abs, scaleCoreVariationLinear_apply, scaleCoreVariationLinear_apply]
    _ ≤ N + |dz| * (4 * (k ^ 2 * y 1 + (y 2 * y 3) / k)) :=
      add_le_add hv (mul_le_mul_of_nonneg_left hfield (abs_nonneg _))
    _ ≤ _ := by unfold partialCoreVariationBudget; dsimp [N] at hN ⊢; nlinarith only [hN]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_clockProjection_bound {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (w : ProjectiveState) :
    ‖scaleCoreVariation k (coreClockProjection y w)‖ ≤
      4 * partialCoreVariationBudget k (y 1) (y 2 * y 3)
        (fderiv ℝ toCoreAngleState y w) (fderiv ℝ projectiveCoreAngle y w) :=
  partialCore_moving_start_bound hk hy hR _ _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_moving_variation_growth {beta v : ℝ → ProjectiveState} {k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b)
    (hbeta : ∀ t ∈ Icc a b, HasDerivAt beta (projectiveOriginalField (beta t)) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (fderiv ℝ projectiveOriginalField (beta t) (v t)) t)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (beta t))
    (hR : coreRadius (beta a 0) (beta a 2) = k) :
    ‖scaleCoreVariation k (coreClockProjection (beta b) (v b))‖ ≤
      4 * coreVariationBound * partialCoreVariationBudget k (beta a 1) (beta a 2 * beta a 3)
        (fderiv ℝ toCoreAngleState (beta a) (v a))
        (fderiv ℝ projectiveCoreAngle (beta a) (v a)) := by
  have H := coreClockProjection_growth hk hab hbeta hv hregion
  have H0 := partialCore_clockProjection_bound hk (hregion a ⟨le_rfl, hab⟩) hR (v a)
  have hC : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  exact H.trans ((mul_le_mul_of_nonneg_right H0 hC).trans_eq (by ring))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_projectedFlowVariation_bound {y : ProjectiveState} {t₀ k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdomain : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hR : coreRadius (projectiveOriginalFlow y t₀ a 0) (projectiveOriginalFlow y t₀ a 2) = k)
    (w : ProjectiveState) :
    let beta := projectiveOriginalFlow y t₀
    let v := projectiveFlowDifferential y t₀ a w
    ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ b w)‖ ≤
      4 * coreVariationBound * partialCoreVariationBudget k (beta a 1) (beta a 2 * beta a 3)
        (fderiv ℝ toCoreAngleState (beta a) v) (fderiv ℝ projectiveCoreAngle (beta a) v) := by
  exact partialCore_moving_variation_growth (beta := projectiveOriginalFlow y t₀)
    (v := fun t => projectiveFlowDifferential y t₀ t w) hk hab
    (fun t ht => hasDerivAt_projectiveOriginalFlow_time hD (hdomain ht) (hA t ht))
    (fun t ht => hasDerivAt_projectiveFlowDifferential_apply hD (hdomain ht) (hA t ht) w)
    hregion hR

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.core_log_lower_bound {k : ℝ} (hk : 6 ≤ k) : 1 ≤ Real.log (4 * k) := by
  have H := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at H
  exact H.trans (Real.log_le_log (by norm_num) (by linarith only [hk]))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_partialCore_entry_variation {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      (∀ t ∈ Icc 0 T, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
        coreRegion k (projectiveOriginalFlow y 0 t)) ∧
      ∀ t ∈ Icc 0 T, ∀ w : ProjectiveState,
        ‖scaleCoreVariation k (coreProjectedFlowVariation y 0 t w)‖ ≤
          4 * coreVariationBound * partialCoreVariationBudget k (y 1) (y 2 * y 3)
            (fderiv ℝ toCoreAngleState y w) (fderiv ℝ projectiveCoreAngle y w) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  let beta := projectiveOriginalFlow y 0
  have hzero : beta 0 = y := projectiveOriginalFlow_initial hD 0
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hR0 : coreRadius (beta 0 0) (beta 0 2) = k := by rw [hzero]; exact hR
  have hV0 : 1 < beta 0 2 ∨ (beta 0 2 = 1 ∧ 1 ≤ beta 0 0) := by
    rw [hzero]
    exact Or.inl hV
  have hU0 : 0 ≤ beta 0 1 ∧ beta 0 1 ≤ (1 / 10000) / k := by
    rw [hzero]
    exact hy.2.2.1
  have hP0 : 0 ≤ beta 0 2 * beta 0 3 ∧ beta 0 2 * beta 0 3 ≤ (1 / 10000) / k := by
    rw [hzero]
    exact hy.2.2.2
  obtain ⟨T, hT, hfirst, _, _, _, _, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk le_rfl hA hR0 hV0 hU0 hP0
  have hreg (t : ℝ) (ht : t ∈ Icc 0 T) :
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧ coreRegion k (beta t) :=
    ⟨lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H t ht).1, (H t ht).2.1⟩
  refine ⟨T, hT, hfirst, hreg, ?_⟩
  intro t ht w
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have Hg := partialCore_projectedFlowVariation_bound hk ht.1 hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (hreg s (hsub hs)).1) (fun s hs => (hreg s (hsub hs)).2) hR0 w
  dsimp only at Hg
  rw [projectiveOriginalFlow_initial hD, projectiveFlowDifferential_initial hD,
    ContinuousLinearMap.id_apply] at Hg
  exact Hg

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_partialCore_radius_response {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      ∃ τ : ProjectiveState → ℝ, τ y = T ∧ ContDiffAt ℝ 2 τ y ∧
        (∀ᶠ z in 𝓝 y,
          IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
            projectiveOriginalFlow z 0 t 2 = 1} (τ z) ∧
          ∀ t ∈ Icc 0 (τ z), t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
            0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 t 0) ∧
        let F := fun z => toCoreAngleState (projectiveOriginalFlow z 0 (τ z))
        ContDiffAt ℝ 2 F y ∧ ∀ w : ProjectiveState,
          let v := fderiv ℝ toCoreAngleState y w
          let dz := fderiv ℝ projectiveCoreAngle y w
          |(fderiv ℝ F y w) 0 - v 0| ≤ 4096 * coreVariationBound *
            (|v 1| + (y 1 + y 2 * y 3) * (|v 0| + |v 2|) / k +
              (k * y 1 + (y 2 * y 3) ^ 2 / k) * |dz|) := by
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  let x := fromProjectiveState y
  let β := projectiveOriginalFlow y 0
  have hzero : β 0 = y := projectiveOriginalFlow_initial hD 0
  have hA0 : 0 < 1 + normalizedMaxCurve x 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hR0 : coreRadius (β 0 0) (β 0 2) = k := by rw [hzero]; exact hR
  have hV0 : 1 < β 0 2 := by rw [hzero]; exact hV
  have hU0 : 0 ≤ β 0 1 ∧ β 0 1 ≤ (1 / 10000) / k := by rw [hzero]; exact hy.2.2.1
  have hP0 : 0 ≤ β 0 2 * β 0 3 ∧ β 0 2 * β 0 3 ≤ (1 / 10000) / k := by
    rw [hzero]
    exact hy.2.2.2
  obtain ⟨T, hT, hfirst, hreg, _⟩ := exists_partialCore_entry_variation hk hy hR hV
  obtain ⟨S, hS, σ, hσ, hcσ, hcP, _, hdP, hnear⟩ :=
    exists_normalized_partialCore_firstReturn_two hc hk le_rfl hA0 hR0 hV0 hU0 hP0
  have hbase := hnear.self_of_nhds
  rw [hσ] at hbase
  have hfirstS : IsLeast {t | 0 < t ∧ β t 2 = 1} S := by
    refine ⟨⟨hS, hbase.1.1.2.2⟩, ?_⟩
    intro t ht
    exact hbase.1.2 ⟨ht.1, normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1.le, ht.2⟩
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hσ hdP
  have htm : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hdown := normalized_core_return_downward hc hk le_rfl hT (hreg T htm).1 hfirst.1.2
    (fun t ht => (hreg t ⟨ht.1.le, ht.2.le⟩).2.2.1)
    (coreRegion_radius_bounds hk (hreg T htm).2).1
    (coreRegion_wall_bounds (hreg T htm).2).1 (coreRegion_wall_bounds (hreg T htm).2).2
  let τ := fun z => σ (fromProjectiveState z)
  let P := fun z => projectiveOriginalFlow z 0 (τ z)
  let F := fun z => toCoreAngleState (P z)
  have hτ : τ y = T := hσ
  have hfrom := contDiffAt_fromProjectiveState 2 (ne_of_gt hD)
  have hcτ : ContDiffAt ℝ 2 τ y := hcσ.comp y hfrom
  have hcP' : ContDiffAt ℝ 2 P y := by
    convert! hcP.comp y hfrom using 1
  have hdP' : HasFDerivAt P (projectiveWallArrivalDifferential y 0 T) y := by
    convert! hdP.comp y ((hfrom.differentiableAt (by norm_num)).hasFDerivAt) using 1
  have hPt : P y = β T := by change projectiveOriginalFlow y 0 (τ y) = β T; rw [hτ]
  have hv : 0 < P y 2 := by rw [hPt]; exact zero_lt_one.trans_le (hreg T htm).2.2.1
  have hcCoord := contDiffAt_toCoreAngleState 2 hv
  have hcF : ContDiffAt ℝ 2 F y := hcCoord.comp y hcP'
  have hdF : HasFDerivAt F
      ((fderiv ℝ toCoreAngleState (β T)).comp (projectiveWallArrivalDifferential y 0 T)) y := by
    have H := (hcCoord.differentiableAt (by norm_num)).hasFDerivAt.comp y hdP'
    rw [hPt] at H
    exact H
  refine ⟨T, hT, hfirst, τ, hτ, hcτ, ?_, hcF, ?_⟩
  · filter_upwards [hfrom.continuousAt.tendsto.eventually hnear] with z hz
    exact ⟨hz.1, hz.2.1⟩
  intro w v dz
  have H := partialCore_wall_arrival_radius_response hk hT.le hD
    (fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1)
    (fun t ht => (hreg t ht).1) (fun t ht => (hreg t ht).2) hR0 hfirst.1.2 hdown.1 w
  dsimp only at H
  rw [projectiveOriginalFlow_initial hD, projectiveFlowDifferential_initial hD,
    ContinuousLinearMap.id_apply] at H
  rw [hdF.fderiv, ContinuousLinearMap.comp_apply]
  exact H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreReturnTime_eq {y : ProjectiveState} {T : ℝ}
    (hT : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1} T) : partialCoreReturnTime y = T := hT.csInf_eq

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreReturnTime_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧ projectiveOriginalFlow z 0 t 2 = 1} (τ z)) :
    partialCoreReturnTime =ᶠ[𝓝 y] τ := hτ.mono fun _ h => partialCoreReturnTime_eq h

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreReturnState_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧ projectiveOriginalFlow z 0 t 2 = 1} (τ z)) :
    partialCoreReturnState =ᶠ[𝓝 y] fun z =>
      let out := projectiveOriginalFlow z 0 (τ z)
      ![coreRadius (out 0) (out 2), out 1, out 3] := by
  filter_upwards [hτ, partialCoreReturnTime_eventuallyEq hτ] with z hz ht
  simp only [partialCoreReturnState, ht, toCoreAngleState, hz.1.2.2, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCore_firstReturn_radius_bounds {k T : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T) :
    let R := coreRadius (projectiveOriginalFlow y 0 T 0) (projectiveOriginalFlow y 0 T 2)
    k / 2 ≤ R ∧ R ≤ 2 * k ∧ |R - k| ≤ 16 * (y 1 + (y 2 * y 3) ^ 2 / k) := by
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have hzero := projectiveOriginalFlow_initial hD (0 : ℝ)
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hR0 : coreRadius (projectiveOriginalFlow y 0 0 0) (projectiveOriginalFlow y 0 0 2) = k := by
    rw [hzero]; exact hR
  have hV0 : 1 < projectiveOriginalFlow y 0 0 2 := by rw [hzero]; exact hV
  have hU0 : 0 ≤ projectiveOriginalFlow y 0 0 1 ∧
      projectiveOriginalFlow y 0 0 1 ≤ (1 / 10000) / k := by rw [hzero]; exact hy.2.2.1
  have hP0 : 0 ≤ projectiveOriginalFlow y 0 0 2 * projectiveOriginalFlow y 0 0 3 ∧
      projectiveOriginalFlow y 0 0 2 * projectiveOriginalFlow y 0 0 3 ≤ (1 / 10000) / k := by
    rw [hzero]; exact hy.2.2.2
  obtain ⟨S, hS, hfirstS, _, _, _, _, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk le_rfl hA hR0 (Or.inl hV0) hU0 hP0
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at H
  have HT := H T ⟨hfirst.1.1.le, le_rfl⟩
  have Hrad := coreRegion_radius_bounds hk HT.2.1
  change 99 / 100 * k ≤ coreRadius (projectiveOriginalFlow y 0 T 0)
    (projectiveOriginalFlow y 0 T 2) ∧ coreRadius (projectiveOriginalFlow y 0 T 0)
    (projectiveOriginalFlow y 0 T 2) ≤ 101 / 100 * k at Hrad
  have Hval := HT.2.2.1
  change |coreRadius (projectiveOriginalFlow y 0 T 0) (projectiveOriginalFlow y 0 T 2) - k| ≤
    16 * (projectiveOriginalFlow y 0 0 1 +
      (projectiveOriginalFlow y 0 0 2 * projectiveOriginalFlow y 0 0 3) ^ 2 / k) at Hval
  rw [hzero] at Hval
  exact ⟨by linarith only [Hrad.1, hk], by linarith only [Hrad.2, hk], Hval⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_partialCore_radial_curve_response {Y : ℝ → ProjectiveState} {x r K : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hY : DifferentiableAt ℝ Y x) :
    let k := fun a => coreRadius (Y a 0) (Y a 2)
    let U := fun a => Y a 1
    let p := fun a => Y a 2 * Y a 3
    let z := fun a => projectiveCoreAngle (Y a)
    let C := 4096 * coreVariationBound
    6 ≤ k x → coreRegion (k x) (Y x) → 1 < Y x 2 →
    2 / (K * r) ≤ k x → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
    |deriv U x| ≤ K * U x / r → |deriv p x| ≤ K * p x / r →
    |deriv z x| ≤ K / r →
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y x) 0 t 2 = 1} T ∧
      ∃ τ : ProjectiveState → ℝ, τ (Y x) = T ∧ ContDiffAt ℝ 2 τ (Y x) ∧
        (∀ᶠ y in 𝓝 (Y x),
          IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
            projectiveOriginalFlow y 0 t 2 = 1} (τ y) ∧
          ∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
            0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0) ∧
        let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
          (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
        DifferentiableAt ℝ f x ∧ k x / 2 ≤ f x ∧ f x ≤ 2 * k x ∧
        DifferentiableAt ℝ (fun a => f a - k a) x ∧
        |f x - k x| ≤ 16 * K * (U x + r * (p x) ^ 2) ∧
        |deriv (fun a => f a - k a) x| ≤ 4 * C * K ^ 2 * (U x + r * p x) / r ^ 2 ∧
        DifferentiableAt ℝ (fun a => 2 / f a - 2 / k a) x ∧
        |2 / f x - 2 / k x| ≤ 32 * K ^ 3 * r ^ 2 * (U x + r * (p x) ^ 2) ∧
        |deriv (fun a => 2 / f a - 2 / k a) x| ≤
          (8 * C * K ^ 4 + 64 * K ^ 5) * (U x + r * p x) := by
  intro k U p z C hk hy hV hklo hkhi hdk hdU hdp hdz
  have hk0 : 0 < k x := by linarith only [hk]
  have hK0 : 0 < K := by linarith only [hK]
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (Real.exp_pos _).le
  have hv : 0 < Y x 2 := zero_lt_one.trans hV
  have hp : 0 ≤ p x ∧ p x ≤ 1 :=
    ⟨hy.2.2.2.1, (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)⟩
  have hki : 1 / k x ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    nlinarith only [H]
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hcF, H⟩ :=
    exists_partialCore_radius_response hk hy rfl hV
  let F := fun y => toCoreAngleState (projectiveOriginalFlow y 0 (τ y))
  let f := fun a => (F (Y a)) 0
  have hin := ((contDiffAt_toCoreAngleState 1 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hz := ((contDiffAt_projectiveCoreAngle 1 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hout := (hcF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hdki : HasDerivAt k (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 0) x := hasDerivAt_pi.mp hin 0
  have hdUi : HasDerivAt U (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 1) x := hasDerivAt_pi.mp hin 1
  have hdpi : HasDerivAt p (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 2) x := hasDerivAt_pi.mp hin 2
  have hdf : HasDerivAt f (fderiv ℝ F (Y x) (deriv Y x) 0) x := hasDerivAt_pi.mp hout 0
  change HasDerivAt z (fderiv ℝ projectiveCoreAngle (Y x) (deriv Y x)) x at hz
  have Hresponse := H (deriv Y x)
  dsimp only at Hresponse
  rw [← hdki.deriv, ← hdUi.deriv, ← hdpi.deriv, ← hz.deriv, ← hdf.deriv] at Hresponse
  have Hbudget := partial_core_radial_derivative_budget hr hK hk0 hki hkhi hy.2.2.1.1 hp hdk hdU hdp hdz
  have Hde : |deriv f x - deriv k x| ≤ 4 * C * K ^ 2 * (U x + r * p x) / r ^ 2 :=
    Hresponse.trans ((mul_le_mul_of_nonneg_left Hbudget hC).trans_eq (by ring))
  have Hvalue := partialCore_firstReturn_radius_bounds hk hy rfl hV hfirst
  change k x / 2 ≤ coreRadius _ _ ∧ coreRadius _ _ ≤ 2 * k x ∧ _ at Hvalue
  have hfval : f x = coreRadius (projectiveOriginalFlow (Y x) 0 T 0) (projectiveOriginalFlow (Y x) 0 T 2) := by
    change coreRadius (projectiveOriginalFlow (Y x) 0 (τ (Y x)) 0) _ = _
    rw [hτ]
  rw [← hfval] at Hvalue
  have Hrec := partial_core_reciprocal_radial_bounds hr hK hy.2.2.1.1 hp
    hdf.differentiableAt hdki.differentiableAt hklo Hvalue.1 Hvalue.2.2 hdk Hde
  refine ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hdf.differentiableAt,
    Hvalue.1, Hvalue.2.1, hdf.differentiableAt.sub hdki.differentiableAt,
    Hrec.2.1, ?_, Hrec.1, Hrec.2.2.1, Hrec.2.2.2⟩
  change |deriv (fun a => f a - k a) x| ≤ _
  rw [deriv_fun_sub hdf.differentiableAt hdki.differentiableAt]
  exact Hde

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_partialCore_multiplier_response {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) :
    ∃ τ : ProjectiveState → ℝ, 0 < τ y ∧ ContDiffAt ℝ 2 τ y ∧
      (∀ᶠ x in 𝓝 y,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState x) 0 ∧
          projectiveOriginalFlow x 0 t 2 = 1} (τ x) ∧
        projectiveOriginalFlow x 0 (τ x) 1 = x 1 * partialCoreReturnMultiplier τ x 0 ∧
        projectiveOriginalFlow x 0 (τ x) 3 = (x 2 * x 3) * partialCoreReturnMultiplier τ x 1) ∧
      (∀ i : Fin 2, 0 < partialCoreReturnMultiplier τ y i ∧
        ContDiffAt ℝ 1 (fun x => Real.log (partialCoreReturnMultiplier τ x i)) y ∧
        ContDiffAt ℝ 1 (fun x => partialCoreReturnMultiplier τ x i) y) ∧
      ∀ w : ProjectiveState,
        let dz := fderiv ℝ projectiveCoreAngle y w
        let Q₀ := partialCoreVariationBudget k (y 1) (y 2 * y 3)
          (fderiv ℝ toCoreAngleState y w) dz
        |fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x 0)) y w| ≤
          40 * coreVariationBound * Real.log (4 * k) * Q₀ + 2 * k * |dz| ∧
        |fderiv ℝ (fun x => Real.log (partialCoreReturnMultiplier τ x 1)) y w| ≤
          236 * coreVariationBound * Real.log (4 * k) * Q₀ / k ^ 2 + 4 * |dz| / k := by
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, _⟩ := exists_partialCore_radius_response hk hy hR hV
  obtain ⟨S, _, hfirstS, hreg, hnorm⟩ := exists_partialCore_entry_variation hk hy hR hV
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hreg hnorm
  have hpos : 0 < τ y := hτ ▸ hT
  have hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0 :=
    fun t ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1
  have hA : ∀ t ∈ Icc 0 (τ y), 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 :=
    fun t ht => (hreg t (hτ ▸ ht)).1
  have hcore : ∀ t ∈ Icc 0 (τ y), coreRegion k (projectiveOriginalFlow y 0 t) :=
    fun t ht => (hreg t (hτ ▸ ht)).2
  have htm : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hdown := normalized_core_return_downward hc hk le_rfl hT (hreg T htm).1 hfirst.1.2
    (fun t ht => (hreg t ⟨ht.1.le, ht.2.le⟩).2.2.1)
    (coreRegion_radius_bounds hk (hreg T htm).2).1
    (coreRegion_wall_bounds (hreg T htm).2).1 (coreRegion_wall_bounds (hreg T htm).2).2
  have hM : projectiveOriginalFlow y 0 (τ y) 0 < 1 := by rw [hτ]; exact hdown.1
  have hhit : ∀ᶠ x in 𝓝 y, projectiveOriginalFlow x 0 (τ x) 2 = 1 :=
    hnear.mono fun _ h => h.1.1.2.2
  have hcτ₁ : ContDiffAt ℝ 1 τ y := hcτ.of_le (by norm_num)
  have hformula := eventually_partialCore_multiplier_formula hk hD hcτ.continuousAt hpos
    (hnear.mono fun _ h => h.2) hcore hhit
  refine ⟨τ, hpos, hcτ, ?_, ?_, ?_⟩
  · filter_upwards [hnear, hformula] with x hx hf
    exact ⟨hx.1, hf⟩
  · intro i
    exact ⟨coreFlowMultiplier_pos _ _ _ _ i,
      contDiffAt_log_partialCoreReturnMultiplier hk hD hcτ₁ hpos.le hdom hA hcore i,
      contDiffAt_partialCoreReturnMultiplier hk hD hcτ₁ hpos.le hdom hA hcore i⟩
  · intro w dz Q₀
    have H := partialCoreReturn_log_derivative_bounds hk hD hcτ₁ hpos.le hdom hA hcore hhit hM w
      (fun t ht => hnorm t (hτ ▸ ht) w)
    constructor
    · exact H.1.trans_eq (by ring)
    · exact H.2.trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCore_radial_multiplier_response {Y : ℝ → ProjectiveState}
    {τ : ProjectiveState → ℝ} {x r K : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hY : DifferentiableAt ℝ Y x)
    (hnear : ∀ᶠ y in 𝓝 (Y x), IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) :
    let k := fun a => coreRadius (Y a 0) (Y a 2)
    let U := fun a => Y a 1
    let p := fun a => Y a 2 * Y a 3
    let z := fun a => projectiveCoreAngle (Y a)
    let m := fun i a => partialCoreReturnMultiplier τ (Y a) i
    let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
    let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
    let A := (200 * coreVariationBound + 2) * K ^ 2
    let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
    let L := Real.log (4 * k x)
    6 ≤ k x → coreRegion (k x) (Y x) → 1 < Y x 2 →
    1 / k x ≤ K * r → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
    |deriv U x| ≤ K * U x / r → |deriv p x| ≤ K * p x / r →
    |deriv z x| ≤ K / r →
    (∀ i : Fin 2, 0 < m i x ∧ DifferentiableAt ℝ (m i) x ∧
      DifferentiableAt ℝ (fun a => Real.log (m i a)) x) ∧
    (fU =ᶠ[𝓝 x] fun a => U a * m 0 a) ∧ (fP =ᶠ[𝓝 x] fun a => p a * m 1 a) ∧
    |deriv (fun a => Real.log (m 0 a)) x| ≤ A * L / r ^ 2 ∧
    |deriv (fun a => Real.log (m 1 a)) x| ≤ B * L ∧
    DifferentiableAt ℝ fU x ∧ DifferentiableAt ℝ fP x ∧ 0 ≤ fU x ∧ 0 ≤ fP x ∧
    |deriv fU x| ≤ fU x * (K / r + A * L / r ^ 2) ∧
    |deriv fP x| ≤ fP x * (K / r + B * L) ∧
    (U x = 0 → fU x = 0 ∧ deriv fU x = 0) ∧
    (p x = 0 → fP x = 0 ∧ deriv fP x = 0) := by
  intro k U p z m fU fP A B L hk hy hV hki hkhi hdk hdU hdp hdz
  have hk0 : 0 < k x := by linarith only [hk]
  have hv : 0 < Y x 2 := zero_lt_one.trans hV
  obtain ⟨σ, _, _, hσnear, hσreg, Hσ⟩ := exists_partialCore_multiplier_response hk hy rfl hV
  have heq : τ =ᶠ[𝓝 (Y x)] σ := by
    filter_upwards [hnear, hσnear] with y hy₁ hy₂
    exact hy₁.unique hy₂.1
  have hmeq (i : Fin 2) : (fun y => partialCoreReturnMultiplier τ y i) =ᶠ[𝓝 (Y x)]
      (fun y => partialCoreReturnMultiplier σ y i) := by
    filter_upwards [heq] with y hy'
    simp only [partialCoreReturnMultiplier, hy']
  have hlogeq (i : Fin 2) : (fun y => Real.log (partialCoreReturnMultiplier τ y i)) =ᶠ[𝓝 (Y x)]
      (fun y => Real.log (partialCoreReturnMultiplier σ y i)) := (hmeq i).mono fun _ h => congrArg Real.log h
  have hmreg (i : Fin 2) : 0 < m i x ∧ DifferentiableAt ℝ (m i) x ∧
      DifferentiableAt ℝ (fun a => Real.log (m i a)) x := by
    have HM := ((hσreg i).2.2.congr_of_eventuallyEq (hmeq i)).differentiableAt (by norm_num)
    have HL := ((hσreg i).2.1.congr_of_eventuallyEq (hlogeq i)).differentiableAt (by norm_num)
    refine ⟨?_, HM.comp x hY, HL.comp x hY⟩
    change 0 < partialCoreReturnMultiplier τ (Y x) i
    have Hval := (hmeq i).self_of_nhds
    dsimp only at Hval
    rw [Hval]
    exact (hσreg i).1
  have hformula : ∀ᶠ a in 𝓝 x, fU a = U a * m 0 a ∧ fP a = p a * m 1 a := by
    filter_upwards [hY.continuousAt.tendsto.eventually hσnear,
      hY.continuousAt.tendsto.eventually heq] with a ha htime
    change projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1 = _ ∧
      projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3 = _
    simpa only [htime, m, partialCoreReturnMultiplier, U, p] using ha.2
  have hin := ((contDiffAt_toCoreAngleState 1 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hz := ((contDiffAt_projectiveCoreAngle 1 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hdk' : HasDerivAt k (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 0) x := hasDerivAt_pi.mp hin 0
  have hdU' : HasDerivAt U (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 1) x := hasDerivAt_pi.mp hin 1
  have hdp' : HasDerivAt p (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 2) x := hasDerivAt_pi.mp hin 2
  change HasDerivAt z (fderiv ℝ projectiveCoreAngle (Y x) (deriv Y x)) x at hz
  have hdl (i : Fin 2) : HasDerivAt (fun a => Real.log (m i a))
      (fderiv ℝ (fun y => Real.log (partialCoreReturnMultiplier σ y i)) (Y x) (deriv Y x)) x :=
    (((hσreg i).2.1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt).congr_of_eventuallyEq
      (hY.continuousAt.tendsto.eventually (hlogeq i))
  have H := Hσ (deriv Y x)
  dsimp only [partialCoreVariationBudget] at H
  rw [← hdk'.deriv, ← hdU'.deriv, ← hdp'.deriv, ← hz.deriv, ← (hdl 0).deriv, ← (hdl 1).deriv] at H
  have hp : 0 ≤ p x ∧ p x ≤ 1 :=
    ⟨hy.2.2.2.1, (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)⟩
  have hku : k x * U x ≤ 1 := by
    have Hku := (le_div_iff₀ hk0).mp hy.2.2.1.2
    change U x * k x ≤ 1 / 10000 at Hku
    nlinarith only [Hku]
  have HQ := partial_core_radial_variation_budget hr hK hk0 hki hkhi hy.2.2.1.1 hku hp hdk hdU hdp hdz
  have Hlog := partial_core_radial_log_bounds hr.1 hK hk0 (Real.exp_pos _).le
    (core_log_lower_bound hk) hki hkhi HQ hdz H.1 H.2
  have HU := multiplier_radial_derivative (a := K / r) hdU'.differentiableAt (hmreg 0).2.1 hy.2.2.1.1 (hmreg 0).1
    (hformula.mono fun _ ha => ha.1) (hdU.trans_eq (by ring)) Hlog.1
  have HP := multiplier_radial_derivative (a := K / r) hdp'.differentiableAt (hmreg 1).2.1 hp.1 (hmreg 1).1
    (hformula.mono fun _ ha => ha.2) (hdp.trans_eq (by ring)) Hlog.2
  exact ⟨hmreg, hformula.mono fun _ ha => ha.1, hformula.mono fun _ ha => ha.2,
    Hlog.1, Hlog.2, HU.1, HP.1, HU.2.1, HP.2.1, HU.2.2.2.1, HP.2.2.2.1,
    HU.2.2.2.2, HP.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCore_firstReturn_contraction {k Z T : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hz : projectiveCoreAngle y ≤ Z)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T) :
    projectiveOriginalFlow y 0 T 1 ≤ y 1 * Real.exp (-k / 12) ∧
      projectiveOriginalFlow y 0 T 3 ≤ y 2 * y 3 := by
  obtain ⟨S, _, hfirstS, hreg, _⟩ := exists_partialCore_entry_variation hk hy hR hV
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hreg
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have hzero := projectiveOriginalFlow_initial hD (0 : ℝ)
  have hz0 : coreAngle (projectiveOriginalFlow y 0 0 0) (projectiveOriginalFlow y 0 0 2) ≤ Z := by
    rw [hzero]
    exact hz
  have H := normalized_partialCore_exit_contraction hc hk le_rfl hfirst.1.1 hZ hkZ
    (fun t ht => (hreg t ht).1) (fun t ht => (hreg t ht).2) hz0 hfirst.1.2
  have HC := H.2.2
  change projectiveOriginalFlow y 0 T 1 ≤ projectiveOriginalFlow y 0 0 1 * Real.exp (-k / 12) ∧
    projectiveOriginalFlow y 0 T 3 ≤ projectiveOriginalFlow y 0 0 2 * projectiveOriginalFlow y 0 0 3 at HC
  rwa [hzero] at HC

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_partialCore_radial_cone {Y : ℝ → ProjectiveState} {x r K D Z : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hD : 0 < D) (hZ : 0 ≤ Z)
    (hY : DifferentiableAt ℝ Y x) :
    let k := fun a => coreRadius (Y a 0) (Y a 2)
    let U := fun a => Y a 1
    let p := fun a => Y a 2 * Y a 3
    let z := fun a => projectiveCoreAngle (Y a)
    let A := (200 * coreVariationBound + 2) * K ^ 2
    let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
    6 ≤ k x → coreRegion (k x) (Y x) → 1 < Y x 2 →
    2 * Real.cosh Z ≤ k x → z x ≤ Z →
    2 / (K * r) ≤ k x → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
    1 / (D * r ^ 2) ≤ -deriv k x →
    |deriv U x| ≤ K * U x / r → |deriv p x| ≤ K * p x / r → |deriv z x| ≤ K / r →
    4 * (4096 * coreVariationBound) * K ^ 2 * (U x + r * p x) ≤ 1 / (2 * D) →
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y x) 0 t 2 = 1} T ∧
      ∃ τ : ProjectiveState → ℝ, τ (Y x) = T ∧ ContDiffAt ℝ 2 τ (Y x) ∧
        (∀ᶠ y in 𝓝 (Y x), IsLeast {t | 0 < t ∧
          t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
        let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
          (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
        let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
        let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
        DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ fU x ∧ DifferentiableAt ℝ fP x ∧
        1 / (2 * D * r ^ 2) ≤ -deriv f x ∧
        |deriv f x| ≤ (K + 1 / (2 * D)) / r ^ 2 ∧
        0 ≤ fU x ∧ 0 ≤ fP x ∧ fU x ≤ U x * Real.exp (-k x / 12) ∧ fP x ≤ p x ∧
        |deriv fU x| ≤ (2 * D * (K + 24 * A) * Real.sqrt (U x)) * Real.sqrt (fU x) * |deriv f x| ∧
        |deriv fP x| ≤ (2 * D * K * (1 + B) * r * Real.sqrt (p x)) * Real.sqrt (fP x) * |deriv f x| ∧
        (U x = 0 → fU x = 0 ∧ deriv fU x = 0) ∧
        (p x = 0 → fP x = 0 ∧ deriv fP x = 0) := by
  intro k U p z A B hk hy hV hkZ hz hklo hkhi hdk hdklo hdU hdp hdz hsmall
  have hr0 := hr.1
  have hK0 : 0 < K := by linarith only [hK]
  have hk0 : 0 < k x := by linarith only [hk]
  have hki : 1 / k x ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    nlinarith only [H]
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hf, _, _, _, _, hde, _⟩ :=
    exists_partialCore_radial_curve_response hr hK hY hk hy hV hklo hkhi hdk hdU hdp hdz
  let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
    (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
  have hkd : DifferentiableAt ℝ k x := by
    have H := ((contDiffAt_toCoreAngleState 1 (zero_lt_one.trans hV)).differentiableAt
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
  have hfirstnear := hnear.mono fun _ h => h.1
  obtain ⟨_, _, _, _, _, hDU, hDP, hu0, hp0, hdu, hdpout, hzeroU, hzeroP⟩ :=
    partialCore_radial_multiplier_response hr hK hY hfirstnear hk hy hV hki hkhi hdk hdU hdp hdz
  have HC := partialCore_firstReturn_contraction hk hy rfl hV hZ hkZ hz hfirst
  rw [← hτ] at HC
  have hA : 0 ≤ A := by dsimp only [A, coreVariationBound]; positivity
  have hB : 0 ≤ B := by dsimp only [B, coreVariationBound]; positivity
  have Hcone := partial_core_radial_cone hr hK0.le hk hkhi hA hB (by positivity : 0 < 2 * D)
    hy.2.2.1.1 hy.2.2.2.1 hu0 hp0 HC.1 HC.2 hdu hdpout (hslope.trans (neg_le_abs _))
  exact ⟨T, hT, hfirst, τ, hτ, hcτ, hfirstnear, hf, hDU, hDP, hslope, hfhi,
    hu0, hp0, HC.1, HC.2, Hcone.1, Hcone.2, hzeroU, hzeroP⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartReturnParameters_eventuallyEq {h s θ ζ ρ : ℝ} {τ : ProjectiveState → ℝ}
    (hY : ContinuousAt (restartFastProjectiveEntry h s θ ζ) ρ)
    (hτ : ∀ᶠ y in 𝓝 (restartFastProjectiveEntry h s θ ζ ρ), IsLeast {t | 0 < t ∧
      t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) :
    restartReturnParameters h s θ ζ =ᶠ[𝓝 ρ] fun a =>
      let out := projectiveOriginalFlow (restartFastProjectiveEntry h s θ ζ a) 0
        (τ (restartFastProjectiveEntry h s θ ζ a))
      coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3] := by
  filter_upwards [hY.tendsto.eventually (partialCoreReturnState_eventuallyEq hτ)] with a ha
  exact congrArg coreExitConnectionParameters ha

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartFastProjectiveEntry_flow {h s θ ζ ρ t : ℝ}
    (hrad : 0 ≤ restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hs : 0 ≤ s) (hA : 0 < restartFastProjectionHeight h s θ ζ ρ) (ht : 0 ≤ t) :
    projectiveOriginalFlow (restartFastProjectiveEntry h s θ ζ ρ) 0 t =
      toProjectiveState (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 (s + t)) := by
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
open Set Filter
open scoped Topology

private theorem BianchiIX.restartFastProjectiveEntry_firstReturn {h s θ ζ ρ T : ℝ}
    (hrad : 0 ≤ restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hs : 0 ≤ s) (hA : 0 < restartFastProjectionHeight h s θ ζ ρ)
    (hfirst : IsLeast {t | 0 < t ∧
      projectiveOriginalFlow (restartFastProjectiveEntry h s θ ζ ρ) 0 t 2 = 1} T) :
    IsLeast {t | s < t ∧ toProjectiveState
      (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 t) 2 = 1} (s + T) := by
  have HF := restartFastProjectiveEntry_flow hrad hs hA hfirst.1.1.le
  refine ⟨⟨by linarith only [hfirst.1.1], ?_⟩, ?_⟩
  · rw [← HF]
    exact hfirst.1.2
  intro t ht
  have hsub : 0 < t - s := sub_pos.mpr ht.1
  have Hflow := restartFastProjectiveEntry_flow hrad hs hA hsub.le
  rw [add_sub_cancel] at Hflow
  have Hleast := hfirst.2 ⟨hsub, by rw [Hflow]; exact ht.2⟩
  linarith only [Hleast]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartPartialCore_radial_cone :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 1 ≤ K ∧ ∃ D : ℝ, 0 < D ∧
        ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let k := restartFastCoreRadius h s θ ζ
            let U := fun a => Y a 1
            let p := fun a => Y a 2 * Y a 3
            let A := (200 * coreVariationBound + 2) * K ^ 2
            let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
            s ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            (∀ t : ℝ, 0 ≤ t → projectiveOriginalFlow (Y ρ) 0 t = toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 (s + t))) ∧
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              IsLeast {t | s < t ∧ toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 t) 2 = 1} (s + T) ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                  t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
                  (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
                let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
                let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
                DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ fU ρ ∧ DifferentiableAt ℝ fP ρ ∧
                1 / (2 * D * r ^ 2) ≤ -deriv f ρ ∧ |deriv f ρ| ≤ (K + 1 / (2 * D)) / r ^ 2 ∧
                0 ≤ fU ρ ∧ 0 ≤ fP ρ ∧ fU ρ ≤ U ρ * Real.exp (-k ρ / 12) ∧ fP ρ ≤ p ρ ∧
                |deriv fU ρ| ≤ (2 * D * (K + 24 * A) * Real.sqrt (U ρ)) * Real.sqrt (fU ρ) * |deriv f ρ| ∧
                |deriv fP ρ| ≤ (2 * D * K * (1 + B) * r * Real.sqrt (p ρ)) * Real.sqrt (fP ρ) * |deriv f ρ| ∧
                (U ρ = 0 → fU ρ = 0 ∧ deriv fU ρ = 0) ∧
                (p ρ = 0 → fP ρ = 0 ∧ deriv fP ρ = 0) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartPartialCore_radial_data
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL
  obtain ⟨K, hK, D, hD, HK⟩ := HH h hh L hL
  have hK0 : 0 < K := by linarith only [hK]
  let C₀ := 4096 * coreVariationBound
  have hC₀ : 0 < C₀ := mul_pos (by norm_num) (Real.exp_pos _)
  refine ⟨K, hK, D, hD, ?_⟩
  intro q P hq hP
  obtain ⟨r₀, hr₀, HR⟩ := HK q P hq hP
  refine ⟨min r₀ (1 / (8 * C₀ * K ^ 3 * D)), lt_min hr₀ (by positivity), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  obtain ⟨hr1, hs, hrad, hdom, hA, hY, hZ, hk6, hz, hy, hV, hsum, hklo, hkhi, hdk, hdklo, hdU, hdp, hdz⟩ :=
    HR r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let k := restartFastCoreRadius h s θ ζ
  have hk : 6 ≤ k ρ := (le_max_left _ _).trans hk6
  have hk0 : 0 < k ρ := by linarith only [hk]
  have hki : 1 / k ρ ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    nlinarith only [H]
  have hsum' : Y ρ 1 + r * (Y ρ 2 * Y ρ 3) ≤ K * r := by
    have H := mul_le_mul_of_nonneg_right hr1 hy.2.2.2.1
    have Hsum := hsum.trans hki
    change Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ K * r at Hsum
    nlinarith only [H, Hsum]
  have hsmall : 4 * C₀ * K ^ 2 * (Y ρ 1 + r * (Y ρ 2 * Y ρ 3)) ≤ 1 / (2 * D) := by
    apply le_trans (mul_le_mul_of_nonneg_left hsum' (by positivity))
    apply (le_div_iff₀ (by positivity : 0 < 2 * D)).mpr
    have H := (le_div_iff₀ (by positivity : 0 < 8 * C₀ * K ^ 3 * D)).mp
      (hr.2.trans (min_le_right _ _))
    nlinarith only [H]
  obtain ⟨T, hT, hfirst, Hτ⟩ := exists_partialCore_radial_cone ⟨hr.1, hr1⟩ hK hD hZ hY
    hk hy hV ((le_max_right _ _).trans hk6) hz hklo hkhi hdk hdklo hdU hdp hdz hsmall
  exact ⟨hdom, fun _ ht => restartFastProjectiveEntry_flow hrad.le hs hA ht,
    T, hT, hfirst, restartFastProjectiveEntry_firstReturn hrad.le hs hA hfirst, Hτ⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartPartialCore_cone_decay :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∀ δ : ℝ, 0 < δ → ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let E := r ^ ((q - 2) / 2) + Real.sqrt (ζ / r)
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              IsLeast {t | s < t ∧ toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 t) 2 = 1} (s + T) ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                  t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
                  (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
                let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
                let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
                DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ fU ρ ∧ DifferentiableAt ℝ fP ρ ∧
                deriv f ρ < 0 ∧ 0 ≤ fU ρ ∧ 0 ≤ fP ρ ∧ C * E ≤ δ ∧
                |deriv fU ρ| ≤ C * E * Real.sqrt (fU ρ) * |deriv f ρ| ∧
                |deriv fP ρ| ≤ C * E * Real.sqrt (fP ρ) * |deriv f ρ| ∧
                |deriv fU ρ| ≤ δ * Real.sqrt (fU ρ) * |deriv f ρ| ∧
                |deriv fP ρ| ≤ δ * Real.sqrt (fP ρ) * |deriv f ρ| ∧
                (0 < fU ρ → 0 < fP ρ →
                  |deriv fU ρ| / (Real.sqrt (fU ρ) * |deriv f ρ|) +
                    |deriv fP ρ| / (Real.sqrt (fP ρ) * |deriv f ρ|) ≤ C * E) ∧
                (ζ = 0 → fP ρ = 0 ∧ deriv fP ρ = 0) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartPartialCore_radial_cone
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  refine ⟨min hC hV, lt_min hhC hhV, ?_⟩
  intro h hh L hL
  have hhC' : h ∈ Ioc (0 : ℝ) hC := ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  have hhV' : h ∈ Ioc (0 : ℝ) hV := ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
  obtain ⟨K, hK, D, hD, HK⟩ := HC h hhC' L hL
  let M := 8 * (L + 1)
  let A := (200 * coreVariationBound + 2) * K ^ 2
  let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
  let CU := 2 * D * (K + 24 * A)
  let CP := 2 * D * K * (1 + B)
  let C := 1 + CU * Real.sqrt (32 * h) + CP * Real.sqrt (2048 * M)
  have hK0 : 0 < K := by linarith only [hK]
  have hM : 0 < M := by dsimp only [M]; positivity
  have hA : 0 ≤ A := by dsimp only [A, coreVariationBound]; positivity
  have hB : 0 ≤ B := by dsimp only [B, coreVariationBound]; positivity
  have hCU : 0 ≤ CU := by dsimp only [CU]; positivity
  have hCP : 0 ≤ CP := by dsimp only [CP]; positivity
  have hCpos : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro q P hq hP δ hδ
  obtain ⟨rC, hrC, HRC⟩ := HK q P hq hP
  obtain ⟨rV, hrV, HRV⟩ := HV h hhV' L hL q (by linarith only [hq])
  obtain ⟨rB, hrB, HRB⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_core_cone_budget hCpos.le (by linarith only [hq]) (by linarith only [hP]) hδ)
  refine ⟨min rC (min rV (min rB 1)), lt_min hrC (lt_min hrV (lt_min hrB (by norm_num))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrV' := hr.2.trans (min_le_right _ _)
  have hrB' := hrV'.trans (min_le_right _ _)
  have hr1 : r ≤ 1 := hrB'.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1
      (by linarith only [hP] : (2 : ℝ) ≤ P)
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let E := r ^ ((q - 2) / 2) + Real.sqrt (ζ / r)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hu, _, hp, _⟩ :=
    HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  change 0 < Y ρ 1 ∧ Y ρ 1 ≤ 32 * h * r ^ (q - 2) at hu
  change 0 ≤ Y ρ 2 * Y ρ 3 ∧ Y ρ 2 * Y ρ 3 ≤ 2048 * M * ζ / r ^ 3 at hp
  have HB : CU * Real.sqrt (Y ρ 1) + CP * r * Real.sqrt (Y ρ 2 * Y ρ 3) ≤ C * E :=
    restart_core_sqrt_budget hr.1 hh.1.le hM.le hζ.1 ⟨hu.1.le, hu.2⟩ hp hCU hCP
      (by dsimp only [C]; linarith)
  have Hδ : C * E ≤ δ := HRB ⟨hr.1, hrB'.trans (min_le_left _ _)⟩ ζ hζ
  have HU : CU * Real.sqrt (Y ρ 1) ≤ C * E := le_trans
    (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hCP hr.1.le) (Real.sqrt_nonneg _))) HB
  have HP : CP * r * Real.sqrt (Y ρ 2 * Y ρ 3) ≤ C * E :=
    le_trans (le_add_of_nonneg_left (by positivity)) HB
  obtain ⟨_, _, T, hT, hfirst, horig, τ, hτ, hcτ, hnear,
    hf, hfu, hfp, hslope, _, hu0, hp0, _, _, hdu, hdp, _, hzeroP⟩ :=
    HRC r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
    (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
  let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
  let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
  have hpos : 0 < 1 / (2 * D * r ^ 2) := by positivity [hr.1]
  have hspeed := hpos.trans_le (hslope.trans (neg_le_abs _))
  have hdu' := hdu.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right HU (Real.sqrt_nonneg _)) (abs_nonneg _))
  have hdp' := hdp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right HP (Real.sqrt_nonneg _)) (abs_nonneg _))
  refine ⟨T, hT, hfirst, horig, τ, hτ, hcτ, hnear, hf, hfu, hfp,
    by linarith only [hslope, hpos], hu0, hp0, Hδ, hdu', hdp', ?_, ?_, ?_, ?_⟩
  · exact hdu'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right Hδ (Real.sqrt_nonneg _)) (abs_nonneg _))
  · exact hdp'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right Hδ (Real.sqrt_nonneg _)) (abs_nonneg _))
  · intro hfu0 hfp0
    have H₁ : |deriv fU ρ| / (Real.sqrt (fU ρ) * |deriv f ρ|) ≤ CU * Real.sqrt (Y ρ 1) :=
      (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hfu0) hspeed)).mpr (hdu.trans_eq (by ring))
    have H₂ : |deriv fP ρ| / (Real.sqrt (fP ρ) * |deriv f ρ|) ≤ CP * r * Real.sqrt (Y ρ 2 * Y ρ 3) :=
      (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hfp0) hspeed)).mpr (hdp.trans_eq (by ring))
    exact (add_le_add H₁ H₂).trans HB
  · intro hz
    have hpzero : Y ρ 2 * Y ρ 3 = 0 := by
      simp only [hz, mul_zero, zero_div] at hp
      exact le_antisymm hp.2 hp.1
    exact hzeroP hpzero

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartReturn_regular :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            ContDiffAt ℝ 2 (restartFastProjectiveEntry h s θ ζ) ρ ∧
              ContDiffAt ℝ 2 (restartReturnParameters h s θ ζ) ρ ∧
              ContDiffAt ℝ 2 (restartReturnState h s θ ζ) ρ ∧
              ContDiffAt ℝ 2 (restartReturnPhase h s θ ζ) ρ ∧
              ContDiffAt ℝ 2 (restartReturnTime h s θ ζ) ρ := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartReturn_joint_regular
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rstar, hrstar, HR⟩ := HH h hh L hL q P hq hP
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  obtain ⟨hY, hp, hG, hf, ht⟩ := HR r hr θ ζ hθ hζ ρ hρ
  have hc : ContDiffAt ℝ 2 (fun a : ℝ => ((θ, ζ), a)) ρ := by fun_prop
  exact ⟨hY.comp ρ hc, hp.comp ρ hc, hG.comp ρ hc, hf.comp ρ hc, ht.comp ρ hc⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartConnection_radial_curve :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                  t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
                let f := fun a => coreRadius (out a 0) (out a 2)
                let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
                let G := fun a => connectionReturnPhysicalState (p a)
                let g := fun a => G a 0
                connectionReturnValid (p ρ) ∧
                connectionReturnState (p ρ) = toProjectiveState
                  (normalizedMaxCurve x 0 (s + T + connectionReturnTime (p ρ))) ∧
                DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ G ρ ∧
                (1 < f ρ ∧ 0 < g ρ) ∧ (deriv f ρ < 0 ∧ deriv g ρ < 0) ∧
                |deriv g ρ / deriv f ρ - 1| ≤ 1 / (4 * p ρ 0) ∧
                (3 / 4 ≤ deriv g ρ / deriv f ρ ∧ deriv g ρ / deriv f ρ ≤ 5 / 4) ∧
                (|deriv (fun a => G a 1) ρ| ≤ Real.sqrt (G ρ 1) * |deriv g ρ| ∧
                  |deriv (fun a => G a 2) ρ| ≤ Real.sqrt (G ρ 2) * |deriv g ρ|) ∧
                DifferentiableAt ℝ (fun a => 2 / f a) ρ ∧
                DifferentiableAt ℝ (fun a => 2 / g a) ρ ∧
                (0 < deriv (fun a => 2 / f a) ρ ∧ 0 < deriv (fun a => 2 / g a) ρ) ∧
                2 / g ρ - 2 / f ρ = -2 * (g ρ - f ρ) / (f ρ * g ρ) ∧
                deriv (fun a => 2 / g a) ρ / deriv (fun a => 2 / f a) ρ =
                  (f ρ / g ρ) ^ 2 * (deriv g ρ / deriv f ρ) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartPartialCore_cone_decay
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_connection
  obtain ⟨ε, hε0, hε, hsε, hεL⟩ := exists_connection_cone_threshold
  refine ⟨min hC hE, lt_min hhC hhE, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨C, _, HC'⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨rC, hrC, HRC⟩ := HC' q P hq hP 1 (by norm_num)
  obtain ⟨rE, hrE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q P hq hP ε ⟨hε0, hε⟩
  refine ⟨min rC rE, lt_min hrC hrE, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  obtain ⟨T, hT, hfirst, _, τ, hτ, hcτ, hnear, hf, hu, hw, hdf, _, _, _, _, _, hdu, hdw, _⟩ :=
    HRC r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ ⟨hζ.1.le, hζ.2⟩ ρ hρ
  obtain ⟨S, _, hfirstS, _, _, hμ, hu0, hw0, _, _, hphase, hvalid, _, _, horbit⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩ θ ζ hθ hζ ρ hρ
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hμ hu0 hw0 hphase hvalid horbit
  let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
  let f := fun a => coreRadius (out a 0) (out a 2)
  let u := fun a => out a 1
  let w := fun a => out a 3
  let p := fun a => coreExitConnectionParameters ![f a, u a, w a]
  let G := fun a => connectionReturnPhysicalState (p a)
  let g := fun a => G a 0
  have hout : out ρ = projectiveOriginalFlow (Y ρ) 0 T := by dsimp only [out]; rw [hτ]
  have houtV : out ρ 2 = 1 := by rw [hout]; exact hfirst.1.2
  have hZ : ![f ρ, u ρ, w ρ] = toCoreAngleState (out ρ) := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change out ρ 3 = out ρ 2 * out ρ 3
      rw [houtV, one_mul]
  have hp : p ρ = coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T)) := by
    change coreExitConnectionParameters ![f ρ, u ρ, w ρ] = _
    rw [hZ, hout]
  rw [← hp] at hμ hu0 hw0 hphase hvalid horbit
  have hphase' : phaseNorm (p ρ 0 + 1) 1 = f ρ := by
    dsimp only [f]
    rw [hout]
    exact hphase
  have hf1 : 1 < f ρ := by
    have Hb := phaseNorm_ge (b := 1) (show 0 ≤ p ρ 0 + 1 by linarith only [hμ.1])
    rw [hphase'] at Hb
    linarith only [hμ.1, Hb]
  have hu0' : 0 < u ρ ∧ u ρ ≤ ε / p ρ 0 := hu0
  have hw0' : 0 < w ρ ∧ w ρ ≤ ε := hw0
  have hdu' : |deriv u ρ| ≤ Real.sqrt (u ρ) * |deriv f ρ| := by simpa only [one_mul] using hdu
  have hdw' : |deriv w ρ| ≤ Real.sqrt (w ρ) * |deriv f ρ| := by simpa only [one_mul] using hdw
  obtain ⟨hG, hdg, hratio, hratioBounds, hgu, hgw⟩ := connectionReturn_coreExit_curve
    hf hu hw hf1 hdf ⟨hε0, hε⟩ hsε hεL hμ.1 hu0' hw0' hdu' hdw'
  have hg : DifferentiableAt ℝ g ρ := (hasDerivAt_pi.mp hG.hasDerivAt 0).differentiableAt
  have hg0 : 0 < g ρ := by
    change 0 < Real.sqrt ((-connectionReturnState (p ρ) 0 - 1) ^ 2 + 1 ^ 2)
    positivity
  have Hrec := reciprocal_curve_identities hf hg (ne_of_gt (lt_trans (by norm_num) hf1)) hg0.ne' (ne_of_lt hdf)
  exact ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hvalid, horbit, hf, hG,
    ⟨hf1, hg0⟩, ⟨hdf, hdg⟩, hratio, hratioBounds, ⟨hgu, hgw⟩, Hrec.1, Hrec.2.1,
    ⟨reciprocal_curve_derivative_pos hf (ne_of_gt (lt_trans (by norm_num) hf1)) hdf,
      reciprocal_curve_derivative_pos hg hg0.ne' hdg⟩, Hrec.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartReturn_control :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let y := restartFastProjectiveEntry h s θ ζ ρ
            let p := restartReturnParameters h s θ ζ ρ
            let G := restartReturnState h s θ ζ ρ
            let f := restartReturnPhase h s θ ζ
            let F := fun a => restartReferenceRadialPhase h (restartRadialCurve θ ζ a)
            IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} (partialCoreReturnTime y) ∧
              ContDiffAt ℝ 2 partialCoreReturnTime y ∧ connectionReturnValid p ∧
              1 / (2 * (8 * (L + 1) + 1) * r) ≤ G 0 ∧ G 0 ≤ 64 / r ∧
              0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 4096 * (8 * (L + 1)) * ζ / r ^ 3 ∧
              coreRadiusEntry G = projectiveReflection (toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0
                  (restartReturnTime h s θ ζ ρ))) ∧
              DifferentiableAt ℝ f ρ ∧ |f ρ - F ρ| ≤ C * r ^ 2 ∧
              |deriv f ρ - deriv F ρ| ≤ C * r ∧
              1 / (8 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ C := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartConnection_output_phase
  obtain ⟨hA, hhA, HA⟩ := exists_restartConnection_output_bounds
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  refine ⟨min hE (min hA hV), lt_min hhE (lt_min hhA hhV), ?_⟩
  intro h hh L hL
  obtain ⟨C, hC, HCE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rE, hrE, HRE⟩ := HCE q P hq hP
  obtain ⟨rA, hrA, HRA⟩ := HA h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨rV, hrV, HRV⟩ := HV h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩ L hL q hq2
  refine ⟨min rE (min rA (min rV 1)), lt_min hrE (lt_min hrA (lt_min hrV (by norm_num))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrA' := hr.2.trans (min_le_right _ _)
  have hrV' := hrA'.trans (min_le_right _ _)
  have hr1 := hrV'.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1.le, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1 (by linarith only [hP] : (2 : ℝ) ≤ P)
  obtain ⟨_, hY, _⟩ := HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨T, _, hfirst, τ, hτ, hcτ, hnear, _, _, hdf, hval, hder, hlo, hhi⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨S, _, hfirstS, hvalid, hradlo, hradhi, hu, hw, hsum, horbit⟩ :=
    HRA r ⟨hr.1, hrA'.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hvalid hradlo hradhi hu hw hsum horbit
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  have heqTime := partialCoreReturnTime_eventuallyEq hnear
  have ht : partialCoreReturnTime (Y ρ) = T := heqTime.self_of_nhds.trans hτ
  have hp : restartReturnParameters h s θ ζ ρ =
      coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T)) := by
    change coreExitConnectionParameters (toCoreAngleState
      (projectiveOriginalFlow (Y ρ) 0 (partialCoreReturnTime (Y ρ)))) = _
    rw [ht]
  have hg : restartReturnState h s θ ζ ρ =
      connectionReturnPhysicalState (coreExitConnectionParameters
        (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T))) := congrArg connectionReturnPhysicalState hp
  have heq := restartReturnParameters_eventuallyEq hY.continuousAt hnear
  have heqPhase : restartReturnPhase h s θ ζ =ᶠ[𝓝 ρ] fun a =>
      let out := projectiveOriginalFlow (Y a) 0 (τ (Y a))
      2 / connectionReturnPhysicalState
        (coreExitConnectionParameters ![coreRadius (out 0) (out 2), out 1, out 3]) 0 :=
    heq.mono fun _ ha => congrArg (fun p => 2 / connectionReturnPhysicalState p 0) ha
  dsimp only [s, Y] at ht hp hg heqPhase
  refine ⟨?_, hcτ.congr_of_eventuallyEq heqTime, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hdf.congr_of_eventuallyEq heqPhase, ?_, ?_, ?_, ?_⟩
  · simpa only [ht] using hfirst
  · simpa only [hp] using hvalid
  · simpa only [hg] using hradlo
  · simpa only [hg] using hradhi
  · simpa only [hg] using hu
  · simpa only [hg] using hw
  · simpa only [hg] using hsum
  · simpa only [restartReturnTime, ht, hp, hg] using horbit
  · simpa only [heqPhase.self_of_nhds] using hval
  · simpa only [heqPhase.deriv_eq] using hder
  · simpa only [heqPhase.deriv_eq] using hlo
  · simpa only [heqPhase.deriv_eq] using hhi

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartReturn_cone :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let G := restartReturnState h s θ ζ
            let k := fun a => G a 0
            ContDiffAt ℝ 2 G ρ ∧ 0 < G ρ 1 ∧ 0 < G ρ 2 ∧
              G ρ 1 + G ρ 2 ≤ 4096 * (8 * (L + 1)) * ζ / r ^ 3 ∧ deriv k ρ < 0 ∧
              |deriv (fun a => G a 1) ρ| ≤ Real.sqrt (G ρ 1) * |deriv k ρ| ∧
              |deriv (fun a => G a 2) ρ| ≤ Real.sqrt (G ρ 2) * |deriv k ρ| := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartReturn_regular
  obtain ⟨hC, hhC, HC⟩ := exists_restartConnection_radial_curve
  obtain ⟨hB, hhB, HB⟩ := exists_restartReturn_control
  refine ⟨min hR (min hC hB), lt_min hhR (lt_min hhC hhB), ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rR, hrR, HRR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨rC, hrC, HRC⟩ := HC h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨_, _, HB'⟩ := HB h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩ L hL
  obtain ⟨rB, hrB, HRB⟩ := HB' q P hq hP
  refine ⟨min rR (min rC rB), lt_min hrR (lt_min hrC hrB), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrCB := hr.2.trans (min_le_right _ _)
  obtain ⟨hcY, _, hcG, _⟩ := HRR r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨_, _, _, τ, _, _, hnear, _, _, _, _, _, hneg, _, _, hcone, _⟩ :=
    HRC r ⟨hr.1, hrCB.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨_, _, _, _, _, hu, hw, hsum, _⟩ :=
    HRB r ⟨hr.1, hrCB.trans (min_le_right _ _)⟩ θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
  let p := fun a => coreExitConnectionParameters
    ![coreRadius (out a 0) (out a 2), out a 1, out a 3]
  have heq := restartReturnParameters_eventuallyEq hcY.continuousAt hnear
  have heqG : restartReturnState h s θ ζ =ᶠ[𝓝 ρ] fun a => connectionReturnPhysicalState (p a) :=
    heq.mono fun _ ha => congrArg connectionReturnPhysicalState ha
  have heqi (i : Fin 3) : (fun a => restartReturnState h s θ ζ a i) =ᶠ[𝓝 ρ]
      fun a => connectionReturnPhysicalState (p a) i :=
    heqG.mono fun _ ha => congrArg (fun z => z i) ha
  have hd0 := (heqi 0).deriv_eq
  have hd1 := (heqi 1).deriv_eq
  have hd2 := (heqi 2).deriv_eq
  have hv1 := (heqi 1).self_of_nhds
  have hv2 := (heqi 2).self_of_nhds
  dsimp only [s, Y, p, out] at hd0 hd1 hd2 hv1 hv2
  refine ⟨hcG, hu, hw, hsum, ?_, ?_, ?_⟩
  · simpa only [hd0] using hneg.2
  · simpa only [hd0, hd1, hv1] using hcone.1
  · simpa only [hd0, hd2, hv2] using hcone.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartReturn_extension :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
            let s := q / 2 * Real.log (1 / r)
            let G := restartReturnState h s θ ζ
            let u := restartAmplitudeExtension h s θ ζ r 1
            let w := restartAmplitudeExtension h s θ ζ r 2
            ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
              (∀ ρ ∈ Icc r (2 * r), u (G ρ 0) = G ρ 1 ∧ w (G ρ 0) = G ρ 2 ∧
                deriv u (G ρ 0) = deriv (fun a => G a 1) ρ / deriv (fun a => G a 0) ρ ∧
                deriv w (G ρ 0) = deriv (fun a => G a 2) ρ / deriv (fun a => G a 0) ρ) ∧
              ∀ k : ℝ, 0 < u k ∧ 0 < w k ∧
                u k + w k ≤ 6400 * (8 * (L + 1)) * ζ / r ^ 3 ∧
                |deriv u k| ≤ Real.sqrt (u k) ∧ |deriv w k| ≤ Real.sqrt (w k) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartReturn_cone
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rstar, hrstar, HR⟩ := HH h hh L hL q P hq hP
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ
  let s := q / 2 * Real.log (1 / r)
  let G := restartReturnState h s θ ζ
  have H (ρ : ℝ) (hρ : ρ ∈ Icc r (2 * r)) := HR r hr θ ζ hθ hζ ρ hρ
  have hG (ρ : ℝ) (hρ : ρ ∈ Icc r (2 * r)) (i : Fin 3) :
      ContDiffAt ℝ 1 (fun a => G a i) ρ := (contDiffAt_pi.mp (H ρ hρ).1 i).of_le (by norm_num)
  have hab : r < 2 * r := by linarith only [hr.1]
  obtain ⟨hcu, hcw, hmatch, hbound⟩ := radiusAmplitudeExtension_pair hab
    (fun ρ hρ => hG ρ hρ 0) (fun ρ hρ => (H ρ hρ).2.2.2.2.1)
    (fun ρ hρ => hG ρ hρ 1) (fun ρ hρ => hG ρ hρ 2)
    (fun ρ hρ => (H ρ hρ).2.1) (fun ρ hρ => (H ρ hρ).2.2.1)
    (fun ρ hρ => (H ρ hρ).2.2.2.2.2.1) (fun ρ hρ => (H ρ hρ).2.2.2.2.2.2)
    (fun ρ hρ => (H ρ hρ).2.2.2.1)
  refine ⟨hcu, hcw, hmatch, ?_⟩
  intro k
  obtain ⟨hu, hw, hsum, hdu, hdw⟩ := hbound k
  exact ⟨hu, hw, hsum.trans_eq (by ring), hdu, hdw⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.measurableSet_restartLabelSet (L r P : ℝ) : MeasurableSet (restartLabelSet L r P) :=
  (measurableSet_le (continuous_abs.comp continuous_fst).measurable measurable_const).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartReturn_extension_measurable :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          let s := q / 2 * Real.log (1 / r)
          Measurable (fun p : restartLabelSet L r P × Icc r (2 * r) =>
            restartReturnState h s p.1.val.1 p.1.val.2 p.2) ∧
            ∀ i : Fin 3, (i = 1 ∨ i = 2) →
              Measurable (fun p : restartLabelSet L r P × ℝ =>
                restartAmplitudeExtension h s p.1.val.1 p.1.val.2 r i p.2) ∧
              Measurable (fun p : restartLabelSet L r P × ℝ =>
                deriv (restartAmplitudeExtension h s p.1.val.1 p.1.val.2 r i) p.2) := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartReturn_joint_regular
  obtain ⟨hC, hhC, HC⟩ := exists_restartReturn_cone
  refine ⟨min hR hC, lt_min hhR hhC, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rR, hrR, HRR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨rC, hrC, HRC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q P hq hP
  refine ⟨min rR rC, lt_min hrR hrC, ?_⟩
  intro r hr
  let s := q / 2 * Real.log (1 / r)
  let X := ↥(restartLabelSet L r P)
  let : StandardBorelSpace X := (measurableSet_restartLabelSet L r P).standardBorel
  let G : X → ℝ → CoreAngleState := fun z a => restartReturnState h s z.val.1 z.val.2 a
  have hmap : Continuous (fun p : X × Icc r (2 * r) => (p.1.val, (p.2 : ℝ))) := by
    dsimp only [X]
    fun_prop
  have hGc : Continuous (fun p : X × Icc r (2 * r) => G p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨_, _, hstate, _⟩ := HRR r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
      p.1.val.1 p.1.val.2 p.1.property.1 p.1.property.2 p.2 p.2.property
    exact hstate.continuousAt.comp
      (f := fun p : X × Icc r (2 * r) => (p.1.val, (p.2 : ℝ))) (x := p) hmap.continuousAt
  have hGm (i : Fin 3) : Measurable (fun p : X × Icc r (2 * r) => G p.1 p.2 i) :=
    ((continuous_apply i).comp hGc).measurable
  have H (z : X) (a : ℝ) (ha : a ∈ Icc r (2 * r)) := HRC r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
    z.val.1 z.val.2 z.property.1 z.property.2 a ha
  have hGtwo (z : X) (a : ℝ) (ha : a ∈ Icc r (2 * r)) (i : Fin 3) :
      ContDiffAt ℝ 2 (fun b => G z b i) a := contDiffAt_pi.mp (H z a ha).1 i
  refine ⟨hGc.measurable, ?_⟩
  intro i hi
  have hpos (z : X) (a : ℝ) (ha : a ∈ Icc r (2 * r)) : 0 < G z a i := by
    rcases hi with rfl | rfl
    · exact (H z a ha).2.1
    · exact (H z a ha).2.2.1
  exact jointly_measurable_radiusAmplitudeExtension (by linarith only [hr.1] : r < 2 * r)
    (hGm 0) (hGm i) (fun z a ha => (hGtwo z a ha 0).of_le (by norm_num))
    (fun z a ha => (H z a ha).2.2.2.2.1)
    (fun z a ha => (hGtwo z a ha i).of_le (by norm_num)) hpos

end
end

/-- The same actual restart, extended curve, and radial phase obey a prescribed era budget. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ Bstar : ℝ, 0 < Bstar →
        ∃ rstar > (0 : ℝ), ∀ r ∈ Ioc (0 : ℝ) rstar,
          let s := q / 2 * Real.log (1 / r)
          Measurable (fun p : restartLabelSet L r P × Icc r (2 * r) =>
            (restartAmplitudeBudget L r p.1.val.2, restartReturnState h s p.1.val.1 p.1.val.2 p.2)) ∧
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
            restartAmplitudeBudget L r ζ ∈ Ioc 0 Bstar ∧
            (restartEraCurve h s θ ζ r).Admissible (restartAmplitudeBudget L r ζ) ∧
            ∀ ρ ∈ Icc r (2 * r),
              restartReturnPhase h s θ ζ ρ ∈ Ioo 0 1 ∧
              DifferentiableAt ℝ (restartReturnPhase h s θ ζ) ρ ∧
              1 / (8 * Real.sqrt 3) ≤ deriv (restartReturnPhase h s θ ζ) ρ ∧
              (restartEraCurve h s θ ζ r).state (2 / restartReturnPhase h s θ ζ ρ) =
                restartReturnState h s θ ζ ρ := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartReturn_extension
  obtain ⟨hC, hhC, HC⟩ := exists_restartReturn_control
  obtain ⟨hM, hhM, HM⟩ := exists_restartReturn_extension_measurable
  refine ⟨min hE (min hC hM), lt_min hhE (lt_min hhC hhM), ?_⟩
  intro h hh L hL q P hq hP Bs hBs
  obtain ⟨rE, hrE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨C, _, HCL⟩ := HC h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ L hL
  obtain ⟨rC, hrC, HRC⟩ := HCL q P hq hP
  obtain ⟨rM, hrM, HRM⟩ := HM h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩ L hL q P hq hP
  let K : ℝ := 6400 * (8 * (L + 1))
  let A : ℝ := 8 * (L + 1) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hAp : 0 < A := by dsimp [A]; positivity
  let rstar := min rE (min rC (min rM (min 1 (min (Bs / K) (1 / (8 * A))))))
  have hrs : 0 < rstar := lt_min hrE (lt_min hrC (lt_min hrM (lt_min (by norm_num)
    (lt_min (div_pos hBs hK) (by positivity)))))
  refine ⟨rstar, hrs, ?_⟩
  intro r hr s
  have hrpos := hr.1
  have hre : r ≤ rE := hr.2.trans (min_le_left _ _)
  have hrc : r ≤ rC := hr.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrm : r ≤ rM := hr.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrrest : r ≤ min 1 (min (Bs / K) (1 / (8 * A))) :=
    hr.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr1 : r ≤ 1 := hrrest.trans (min_le_left _ _)
  have hrB : r ≤ Bs / K := hrrest.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrsmall : r ≤ 1 / (8 * A) := hrrest.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hBm : Measurable (fun p : restartLabelSet L r P × Icc r (2 * r) => restartAmplitudeBudget L r p.1.val.2) := by
    unfold restartAmplitudeBudget
    fun_prop
  refine ⟨hBm.prodMk (HRM r ⟨hr.1, hrm⟩).1, ?_⟩
  intro θ ζ hθ hζ
  have hζpos := hζ.1
  have hζ4 : ζ ≤ r ^ 4 := hζ.2.trans (by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1 (by linarith : (4 : ℝ) ≤ P))
  have hbudget : restartAmplitudeBudget L r ζ ∈ Ioc 0 Bs := by
    refine ⟨by dsimp [restartAmplitudeBudget]; positivity, ?_⟩
    change K * ζ / r ^ 3 ≤ Bs
    calc
      _ ≤ K * r ^ 4 / r ^ 3 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hζ4 hK.le) (by positivity)
      _ = K * r := by field_simp
      _ ≤ Bs := by simpa only [mul_comm] using (le_div_iff₀ hK).mp hrB
  obtain ⟨hu, hw, Hmatch, Hbound⟩ := HRE r ⟨hr.1, hre⟩ θ ζ hθ hζ
  refine ⟨hbudget, ?_, ?_⟩
  · intro k _
    obtain ⟨hup, hwp, hsum, hdu, hdw⟩ := Hbound k
    exact ⟨hup, hwp, hsum, hu.contDiffAt, hw.contDiffAt, hdu, hdw⟩
  · intro ρ hρ
    obtain ⟨_, _, _, hklo, _, _, _, _, _, hdf, _, _, hdlo, _⟩ :=
      HRC r ⟨hr.1, hrc⟩ θ ζ hθ hζ ρ hρ
    have hmul : r * (8 * A) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 8 * A)).mp hrsmall
    have hkfour : 4 ≤ restartReturnState h s θ ζ ρ 0 := (show 4 ≤ 1 / (2 * A * r) by
      apply (le_div_iff₀ (by positivity : 0 < 2 * A * r)).mpr
      nlinarith).trans hklo
    have hkpos : 0 < restartReturnState h s θ ζ ρ 0 := by linarith
    have hfunit : restartReturnPhase h s θ ζ ρ ∈ Ioo 0 1 :=
      ⟨div_pos (by norm_num) hkpos, (div_lt_one hkpos).mpr (by linarith)⟩
    refine ⟨hfunit, hdf, hdlo, ?_⟩
    have hrec : 2 / restartReturnPhase h s θ ζ ρ = restartReturnState h s θ ζ ρ 0 := by
      change 2 / (2 / restartReturnState h s θ ζ ρ 0) = _
      field_simp
    rw [hrec]
    funext i
    fin_cases i
    · rfl
    · exact (Hmatch ρ hρ).1
    · exact (Hmatch ρ hρ).2.1
