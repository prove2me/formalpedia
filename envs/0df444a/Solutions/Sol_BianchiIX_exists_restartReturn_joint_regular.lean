-- Prove2me | solution 1 for BianchiIX.exists_restartReturn_joint_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:51:52.423609+00:00
-- url     : https://prove2.me/submissions/97ae0ba0-db13-4498-b1e5-a0e36ec9d918

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_contDiffAt_scalar_event_branch
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuousAt_activeWall_event_rate
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreClockProjection_growth
import Theorems.Thm_BianchiIX_eventually_activeWall_interior_first_hit
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_exists_normalized_partialCore_return
import Theorems.Thm_BianchiIX_exists_restartFastProjectionError_bounds
import Theorems.Thm_BianchiIX_exists_restartFastProjectiveEntry_bounds
import Theorems.Thm_BianchiIX_exists_restartPartialCore_connection
import Theorems.Thm_BianchiIX_exists_restartSection_radial_approximation
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_core_residence
import Theorems.Thm_BianchiIX_normalized_core_return_downward
import Theorems.Thm_BianchiIX_normalized_core_return_isLeast
import Theorems.Thm_BianchiIX_normalized_partialCore_energy_band_improves
import Theorems.Thm_BianchiIX_partialCore_field_bounds
import Theorems.Thm_BianchiIX_partialCore_wall_arrival_radius_response
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_reciprocal_radial_bounds
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

private theorem BianchiIX.restartReferenceRoot_sq {n : ℝ} (hn : n ^ 2 ≤ 1) :
    restartReferenceRoot n ^ 2 = 1 - n ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hn)

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

private theorem BianchiIX.restart_coefficients_small {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) :
    0 ≤ restartShearFactor n - 1 ∧ restartShearFactor n - 1 ≤ n ∧
      0 ≤ restartWallFactor n - 1 ∧ restartWallFactor n - 1 ≤ n ∧
      0 ≤ restartShearCoupling n ∧ restartShearCoupling n ≤ n := by
  let z := restartReferenceRoot n
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : z ^ 2 = 1 - n ^ 2 := restartReferenceRoot_sq (by nlinarith only [hn.1, hn.2])
  have hz1 : z ≤ 1 := by nlinarith only [hz0, hz2, sq_nonneg n]
  have hzhalf : 1 / 2 ≤ z := by nlinarith only [hz0, hz2, hn.1, hn.2]
  have hzsmall : 1 - z ≤ n := by
    nlinarith only [hz2, hn.1, hn.2, mul_nonneg hz0 (sub_nonneg.mpr hz1)]
  have hd : 0 < 2 + z := by positivity
  have hd2 : 0 < 2 * (2 + z) ^ 2 := by positivity
  have ha : restartShearFactor n - 1 = (1 - z) / (2 + z) := by
    dsimp only [restartShearFactor]
    change 3 / (2 + z) - 1 = _
    field_simp
    ring
  have hc : restartWallFactor n - 1 = (1 - z) * (2 * z + 1) / (2 * (2 + z) ^ 2) := by
    dsimp only [restartWallFactor]
    change 9 * (1 + z) / (2 * (2 + z) ^ 2) - 1 = _
    field_simp
    ring
  have ha0 : 0 ≤ restartShearFactor n - 1 := by rw [ha]; positivity
  have ha1 : restartShearFactor n - 1 ≤ n := by
    rw [ha]
    apply le_trans _ hzsmall
    apply (div_le_iff₀ hd).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hz1) (show 0 ≤ 1 + z by positivity)]
  have hc0 : 0 ≤ restartWallFactor n - 1 := by rw [hc]; positivity
  have hc1 : restartWallFactor n - 1 ≤ n := by
    rw [hc]
    apply le_trans _ hzsmall
    apply (div_le_iff₀ hd2).mpr
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hz0, sq_nonneg z]) (sub_nonneg.mpr hz1)
  have hk0 : 0 ≤ restartShearCoupling n := by
    dsimp only [restartShearCoupling]
    exact div_nonneg (mul_nonneg (by positivity) hn.1) (sq_nonneg _)
  have hk1 : restartShearCoupling n ≤ n := by
    dsimp only [restartShearCoupling]
    change 3 * Real.sqrt 3 * n / (2 + z) ^ 2 ≤ n
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    have H : 3 * Real.sqrt 3 ≤ (2 + z) ^ 2 := by
      nlinarith only [hsqrt, hzhalf, sq_nonneg (z - 1 / 2)]
    nlinarith only [mul_le_mul_of_nonneg_right H hn.1]
  exact ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩

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

private theorem BianchiIX.abs_quadraticFromCoefficients_le (m : Fin 3 → ℝ) (s v : ℝ) :
    |quadraticFromCoefficients m s v| ≤ 2 * ‖m‖ * (s ^ 2 + v ^ 2) := by
  have hm (i : Fin 3) : |m i| ≤ ‖m‖ := norm_le_pi_norm m i
  have hsv : |s| * |v| ≤ s ^ 2 + v ^ 2 := by
    nlinarith only [sq_nonneg (|s| - |v|), sq_abs s, sq_abs v, sq_nonneg s, sq_nonneg v]
  calc
    _ ≤ |m 0 * s ^ 2| + |m 1 * s * v| + |m 2 * v ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖m‖ * s ^ 2 + ‖m‖ * (|s| * |v|) + ‖m‖ * v ^ 2 := by
      simp only [abs_mul, abs_sq, mul_assoc]
      gcongr
      · exact hm 0
      · exact hm 1
      · exact hm 2
    _ ≤ 2 * ‖m‖ * (s ^ 2 + v ^ 2) := by
      nlinarith only [mul_le_mul_of_nonneg_left hsv (norm_nonneg m)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

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

private theorem BianchiIX.restartQuadratic_relative_error {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) (s v : ℝ) :
    |restartQuadratic n s v - (s ^ 2 + v ^ 2)| ≤ 8 * n * (s ^ 2 + v ^ 2) := by
  obtain ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩ := restart_coefficients_small hn
  have hn2 : n ^ 2 ≤ n := by nlinarith only [hn.1, hn.2]
  have haSq := mul_self_le_mul_self (by linarith only [ha0] : 0 ≤ restartShearFactor n)
    (by linarith only [ha1] : restartShearFactor n ≤ 1 + n)
  have hcSq := mul_self_le_mul_self (by linarith only [hc0] : 0 ≤ restartWallFactor n)
    (by linarith only [hc1] : restartWallFactor n ≤ 1 + n)
  have hkSq := mul_self_le_mul_self hk0 hk1
  have hak := mul_le_mul ha1 hk1 hk0 hn.1
  let m : Fin 3 → ℝ := ![restartShearFactor n ^ 2 - 1,
    2 * restartShearFactor n * restartShearCoupling n,
    restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - 1]
  have hm : ‖m‖ ≤ 4 * n := by
    apply (pi_norm_le_iff_of_nonneg (by positivity [hn.1] : 0 ≤ 4 * n)).mpr
    intro i
    fin_cases i <;> apply abs_le.mpr <;> constructor
    · change -(4 * n) ≤ restartShearFactor n ^ 2 - 1
      nlinarith only [ha0, hn.1]
    · change restartShearFactor n ^ 2 - 1 ≤ 4 * n
      nlinarith only [haSq, hn2, hn.1]
    · change -(4 * n) ≤ 2 * restartShearFactor n * restartShearCoupling n
      nlinarith only [mul_nonneg (by linarith only [ha0] : 0 ≤ restartShearFactor n) hk0, hn.1]
    · change 2 * restartShearFactor n * restartShearCoupling n ≤ 4 * n
      nlinarith only [hak, hk1, hn2]
    · change -(4 * n) ≤ restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - 1
      nlinarith only [hc0, sq_nonneg (restartShearCoupling n), hn.1]
    · change restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - 1 ≤ 4 * n
      nlinarith only [hcSq, hkSq, hn2]
  have heq : restartQuadratic n s v - (s ^ 2 + v ^ 2) = quadraticFromCoefficients m s v := by
    dsimp [restartQuadratic, quadraticFromCoefficients, m]
    ring
  rw [heq]
  exact (abs_quadraticFromCoefficients_le m s v).trans (by
    nlinarith only [mul_le_mul_of_nonneg_right hm (add_nonneg (sq_nonneg s) (sq_nonneg v))])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartQuadratic_upper {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) (s v : ℝ) :
    restartQuadratic n s v ≤ 2 * (s ^ 2 + v ^ 2) := by
  have H := (le_abs_self _).trans (restartQuadratic_relative_error hn s v)
  have Hn := mul_le_mul_of_nonneg_right hn.2 (add_nonneg (sq_nonneg s) (sq_nonneg v))
  nlinarith only [H, Hn, sq_nonneg s, sq_nonneg v]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sqrt_restartQuadratic_le_radius {n r s v : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16)
    (hr : 0 ≤ r) (hs : |s| ≤ r) (hv : |v| ≤ 2 * r) :
    Real.sqrt (restartQuadratic n s v) ≤ 4 * r := by
  have hs2 := mul_self_le_mul_self (abs_nonneg s) hs
  have hv2 := mul_self_le_mul_self (abs_nonneg v) hv
  have HJ : 0 ≤ restartQuadratic n s v := add_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith only [restartQuadratic_upper hn s v, Real.sq_sqrt HJ, Real.sqrt_nonneg (restartQuadratic n s v),
    hs2, hv2, sq_abs s, sq_abs v, hr, sq_nonneg r]

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

private theorem BianchiIX.phaseNorm_le_abs_add (a b : ℝ) : phaseNorm a b ≤ |a| + |b| := by
  have hr : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hs := phaseNorm_sq a b
  nlinarith only [hr, hs, sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_cauchy (a b c d : ℝ) :
    |a * c + b * d| ≤ phaseNorm a b * phaseNorm c d := by
  have hP : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hQ : 0 ≤ phaseNorm c d := Real.sqrt_nonneg _
  have hsq : (a * c + b * d) ^ 2 ≤ (phaseNorm a b * phaseNorm c d) ^ 2 := by
    rw [mul_pow, phaseNorm_sq, phaseNorm_sq]
    nlinarith only [sq_nonneg (a * d - b * c)]
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hP hQ)).mp (by simpa using hsq)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_phaseNorm_affine_bounds {a b c d ρ ζ : ℝ}
    (hP : 0 < phaseNorm a b) (hρ : 0 < ρ) (hζ : 0 ≤ ζ)
    (hsmall : 3 * ζ * phaseNorm c d ≤ ρ * phaseNorm a b) :
    ∃ v : ℝ,
      HasDerivAt (fun x : ℝ => phaseNorm (a * x - c * ζ) (b * x - d * ζ)) v ρ ∧
      phaseNorm a b / 2 ≤ v ∧ v ≤ phaseNorm a b := by
  let P := phaseNorm a b
  let Q := phaseNorm c d
  let R := phaseNorm (a * ρ - c * ζ) (b * ρ - d * ζ)
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hC := (abs_le.mp (phaseNorm_cauchy a b c d)).2
  have hC' := (abs_le.mp (phaseNorm_cauchy a b c d)).1
  have hRsq : R ^ 2 = (ρ * P) ^ 2 - 2 * ρ * ζ * (a * c + b * d) + (ζ * Q) ^ 2 := by
    dsimp only [R, P, Q]
    rw [phaseNorm_sq, mul_pow, mul_pow, phaseNorm_sq, phaseNorm_sq]
    ring
  have hPQ : 0 < ρ * P := mul_pos hρ hP
  have hlowpos : 0 < ρ * P - ζ * Q := by
    change 3 * ζ * Q ≤ ρ * P at hsmall
    nlinarith only [hsmall, hPQ, mul_nonneg hζ hQ]
  have hcross := mul_le_mul_of_nonneg_left hC (show 0 ≤ 2 * ρ * ζ by positivity)
  have hcross' := mul_le_mul_of_nonneg_left hC' (show 0 ≤ 2 * ρ * ζ by positivity)
  change _ ≤ 2 * ρ * ζ * (P * Q) at hcross
  change 2 * ρ * ζ * (-(P * Q)) ≤ _ at hcross'
  have hlow : ρ * P - ζ * Q ≤ R := by
    nlinarith only [hRsq, hcross, hlowpos, hR]
  have hupp : R ≤ ρ * P + ζ * Q := by
    nlinarith only [hRsq, hcross', hPQ, mul_nonneg hζ hQ, hR]
  have hRpos : 0 < R := hlowpos.trans_le hlow
  have hnz : (a * ρ - c * ζ) ^ 2 + (b * ρ - d * ζ) ^ 2 ≠ 0 := by
    have H := phaseNorm_sq (a * ρ - c * ζ) (b * ρ - d * ζ)
    change R ^ 2 = _ at H
    nlinarith only [H, sq_pos_of_pos hRpos]
  let v := (a * (a * ρ - c * ζ) + b * (b * ρ - d * ζ)) / R
  have Hv : HasDerivAt (fun x : ℝ => phaseNorm (a * x - c * ζ) (b * x - d * ζ)) v ρ := by
    have Ha := ((hasDerivAt_id ρ).const_mul a).sub_const (c * ζ)
    have Hb := ((hasDerivAt_id ρ).const_mul b).sub_const (d * ζ)
    convert! ((Ha.pow 2).add (Hb.pow 2)).sqrt hnz using 1
    dsimp only [v, R, phaseNorm]
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  have hid : a * (a * ρ - c * ζ) + b * (b * ρ - d * ζ) = ρ * P ^ 2 - ζ * (a * c + b * d) := by
    dsimp only [P]
    rw [phaseNorm_sq]
    ring
  refine ⟨v, Hv, (le_div_iff₀ hRpos).mpr ?_, (div_le_iff₀ hRpos).mpr ?_⟩
  · have H₁ := mul_le_mul_of_nonneg_left hC hζ
    have H₂ := mul_le_mul_of_nonneg_left hupp hP.le
    have H₃ := mul_le_mul_of_nonneg_left hsmall hP.le
    change _ ≤ ζ * (P * Q) at H₁
    rw [hid]
    nlinarith only [H₁, H₂, H₃]
  · exact (abs_le.mp (phaseNorm_cauchy a b (a * ρ - c * ζ) (b * ρ - d * ζ))).2

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

private theorem BianchiIX.partialCoreReturn_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) :
    IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} (partialCoreReturnTime y) ∧
      ContDiffAt ℝ 2 partialCoreReturnTime y ∧ ContDiffAt ℝ 2 partialCoreReturnState y ∧
      (∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧
        t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧ projectiveOriginalFlow z 0 t 2 = 1}
          (partialCoreReturnTime z) ∧
        ∀ t ∈ Icc 0 (partialCoreReturnTime z), t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 t 0) := by
  obtain ⟨T, _, hfirst, τ, hτ, hcτ, hnear, hcF, _⟩ :=
    exists_partialCore_radius_response hk hy hR hV
  have heq := partialCoreReturnTime_eventuallyEq (hnear.mono fun _ h => h.1)
  have hstate : partialCoreReturnState =ᶠ[𝓝 y] fun z =>
      toCoreAngleState (projectiveOriginalFlow z 0 (τ z)) := by
    filter_upwards [heq] with z hz
    simp only [partialCoreReturnState, hz]
  refine ⟨?_, hcτ.congr_of_eventuallyEq heq, hcF.congr_of_eventuallyEq hstate, ?_⟩
  · rw [heq.self_of_nhds, hτ]
    exact hfirst
  · filter_upwards [hnear, heq] with z hz ht
    simpa only [ht] using hz

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
open Set

private theorem BianchiIX.hasDerivAt_restartRadialCurve (θ ζ ρ : ℝ) :
    HasDerivAt (restartRadialCurve θ ζ) (restartRadialDirection θ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartRadialCurve, restartRadialDirection] using (hasDerivAt_id ρ).const_mul θ
  · convert! hasDerivAt_id ρ using 1
  · simpa [restartRadialCurve, restartRadialDirection] using hasDerivAt_const ρ ζ

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartRadialDirection_norm_le {θ L : ℝ} (hL : 0 ≤ L) (hθ : |θ| ≤ L) :
    ‖restartRadialDirection θ‖ ≤ L + 1 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ L + 1)).mpr
  intro i
  fin_cases i
  · change |θ| ≤ L + 1
    linarith only [hθ]
  · change |(1 : ℝ)| ≤ L + 1
    rw [abs_one]
    linarith only [hL]
  · change |(0 : ℝ)| ≤ L + 1
    rw [abs_zero]
    positivity

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartRadialCurve_annulus {r ρ θ ζ L : ℝ} (hr : 0 < r)
    (hρ : ρ ∈ Icc r (2 * r)) (hL : 0 ≤ L) (hθ : |θ| ≤ L)
    (hζ : 0 ≤ ζ ∧ ζ ≤ r / 9) :
    ‖restartRadialCurve θ ζ ρ‖ ≤ (2 * (L + 1)) * r ∧
      r / 2 ≤ restartRadialNorm (restartRadialCurve θ ζ ρ) := by
  have hρ0 : 0 < ρ := hr.trans_le hρ.1
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2 * (L + 1)) * r)).mpr
    intro i
    fin_cases i
    · change |θ * ρ| ≤ _
      rw [abs_mul, abs_of_pos hρ0]
      have H := mul_le_mul hθ hρ.2 hρ0.le hL
      nlinarith only [H, hr]
    · change |ρ| ≤ _
      rw [abs_of_pos hρ0]
      nlinarith only [hρ.2, mul_nonneg hL hr.le]
    · change |ζ| ≤ _
      rw [abs_of_nonneg hζ.1]
      nlinarith only [hζ.2, hr, mul_nonneg hL hr.le]
  · have hdiff : 0 ≤ ρ - ζ := by linarith only [hρ.1, hζ.2, hr]
    have H := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg (θ * ρ)) :
      (ρ - ζ) ^ 2 ≤ (θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    rw [Real.sqrt_sq hdiff] at H
    change r / 2 ≤ Real.sqrt ((θ * ρ) ^ 2 + (ρ - ζ) ^ 2)
    linarith only [H, hρ.1, hζ.2, hr]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartReferenceRadialPhase_curve (h θ ζ ρ : ℝ) :
    restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ) =
      phaseNorm ((restartShearFactor h * θ + restartShearCoupling h) * ρ -
        restartShearCoupling h * ζ) (restartWallFactor h * ρ - restartWallFactor h * ζ) /
          Real.sqrt 3 := by
  change Real.sqrt ((restartShearFactor h * (θ * ρ) + restartShearCoupling h * (ρ - ζ)) ^ 2 +
    (restartWallFactor h * (ρ - ζ)) ^ 2) / Real.sqrt 3 = _
  unfold phaseNorm
  congr 2
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartReferenceRadialPhase_curve_derivative {h θ ζ ρ L : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (_hL : 0 ≤ L) (hθ : |θ| ≤ L)
    (hρ : 0 < ρ) (hζ : 0 ≤ ζ ∧ ζ ≤ ρ / 9) :
    DifferentiableAt ℝ (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ ∧
      1 / (2 * Real.sqrt 3) ≤
        deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ ∧
      deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ ≤
        (2 * L + 3) / Real.sqrt 3 := by
  obtain ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩ := restart_coefficients_small hh
  let a := restartShearFactor h
  let c := restartWallFactor h
  let k := restartShearCoupling h
  have ha : 1 ≤ a ∧ a ≤ 2 := by dsimp only [a]; constructor <;> linarith only [ha0, ha1, hh.2]
  have hc : 1 ≤ c ∧ c ≤ 2 := by dsimp only [c]; constructor <;> linarith only [hc0, hc1, hh.2]
  have hk : 0 ≤ k ∧ k ≤ 1 := ⟨hk0, hk1.trans (by linarith only [hh.2])⟩
  have hP : 1 ≤ phaseNorm (a * θ + k) c := by
    have H := phaseNorm_ge (b := a * θ + k) (by linarith only [hc.1] : 0 ≤ c)
    have heq : phaseNorm c (a * θ + k) = phaseNorm (a * θ + k) c := by
      simp only [phaseNorm, add_comm]
    rw [heq] at H
    exact hc.1.trans H
  have hQ : phaseNorm k c ≤ 3 := by
    have H := phaseNorm_le_abs_add k c
    rw [abs_of_nonneg hk.1, abs_of_nonneg (by linarith only [hc.1] : 0 ≤ c)] at H
    linarith only [H, hk.2, hc.2]
  have hPupper : phaseNorm (a * θ + k) c ≤ 2 * L + 3 := by
    have H := phaseNorm_le_abs_add (a * θ + k) c
    have Hθ := mul_le_mul ha.2 hθ (abs_nonneg θ) (by norm_num : (0 : ℝ) ≤ 2)
    have Hsum := abs_add_le (a * θ) k
    rw [abs_mul, abs_of_nonneg (by linarith only [ha.1] : 0 ≤ a), abs_of_nonneg hk.1] at Hsum
    rw [abs_of_nonneg (by linarith only [hc.1] : 0 ≤ c)] at H
    linarith only [H, Hθ, Hsum, hk.2, hc.2]
  have hsmall : 3 * ζ * phaseNorm k c ≤ ρ * phaseNorm (a * θ + k) c := by
    have H := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 3 * ζ by positivity [hζ.1])
    have H' := mul_le_mul_of_nonneg_left hP hρ.le
    nlinarith only [H, H', hζ.2]
  obtain ⟨v, Hv, hvlow, hvup⟩ := hasDerivAt_phaseNorm_affine_bounds
    (show 0 < phaseNorm (a * θ + k) c by linarith only [hP]) hρ hζ.1 hsmall
  have Href : HasDerivAt (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x))
      (v / Real.sqrt 3) ρ := by
    simpa only [restartReferenceRadialPhase_curve, a, c, k] using Hv.div_const (Real.sqrt 3)
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨Href.differentiableAt, ?_, ?_⟩ <;> rw [Href.deriv]
  · have H : (1 : ℝ) / 2 ≤ v := by linarith only [hP, hvlow]
    calc
      _ = (1 / 2) / Real.sqrt 3 := by ring
      _ ≤ v / Real.sqrt 3 := div_le_div_of_nonneg_right H hsqrt.le
  · exact div_le_div_of_nonneg_right (hvup.trans hPupper) hsqrt.le

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastRadialPhase_derivative {h T θ ζ ρ L ε : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (hL : 0 ≤ L) (hθ : |θ| ≤ L)
    (hρ : 0 < ρ) (hζ : 0 ≤ ζ ∧ ζ ≤ ρ / 9) (hε : 0 ≤ ε)
    (HD : DifferentiableAt ℝ (restartSectionRadialError h T) (restartRadialCurve θ ζ ρ))
    (HB : ‖fderiv ℝ (restartSectionRadialError h T) (restartRadialCurve θ ζ ρ)‖ ≤ ε) :
    DifferentiableAt ℝ (restartFastRadialPhase h T θ ζ) ρ ∧
      |deriv (restartFastRadialPhase h T θ ζ) ρ -
        deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ| ≤ ε * (L + 1) := by
  have Href := (restartReferenceRadialPhase_curve_derivative hh hL hθ hρ hζ).1.hasDerivAt
  have Herr := HD.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_restartRadialCurve θ ζ ρ)
  have Hsum : HasDerivAt (restartFastRadialPhase h T θ ζ)
      ((fderiv ℝ (restartSectionRadialError h T) (restartRadialCurve θ ζ ρ)) (restartRadialDirection θ) +
        deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ) ρ := by
    convert! Herr.add Href using 1
    ext x
    simp only [Function.comp_apply, Pi.add_apply, restartSectionRadialError, restartFastRadialPhase,
      sub_add_cancel]
  refine ⟨Hsum.differentiableAt, ?_⟩
  rw [Hsum.deriv, add_sub_cancel_right]
  exact ((fderiv ℝ (restartSectionRadialError h T) (restartRadialCurve θ ζ ρ)).le_opNorm _).trans
    (mul_le_mul HB (restartRadialDirection_norm_le hL hθ) (norm_nonneg _) hε)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartFastRadialPhase_monotone :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r / 9) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastRadialPhase h T θ ζ) ρ ∧
            |restartFastRadialPhase h T θ ζ ρ -
              restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ)| ≤ K * r ^ 2 ∧
            |deriv (restartFastRadialPhase h T θ ζ) ρ -
              deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ| ≤ K * r ∧
            1 / (4 * Real.sqrt 3) ≤ deriv (restartFastRadialPhase h T θ ζ) ρ ∧
            deriv (restartFastRadialPhase h T θ ζ) ρ ≤ (2 * L + 3) / Real.sqrt 3 + 1 := by
  obtain ⟨h₀, hh₀, H₀⟩ := exists_restartSection_radial_approximation
  refine ⟨min h₀ (1 / 16), lt_min hh₀ (by norm_num), ?_⟩
  intro h hh L hL
  have hhsmall : 0 ≤ h ∧ h ≤ 1 / 16 := ⟨hh.1.le, hh.2.trans (min_le_right _ _)⟩
  obtain ⟨A, hA, HA⟩ := H₀ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    (1 / 2) (2 * (L + 1)) (by norm_num) (by positivity)
  let K := A * (L + 1)
  have hK : 0 < K := mul_pos hA (by positivity)
  have hAK : A ≤ K := by dsimp only [K]; nlinarith only [mul_nonneg hA.le hL]
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨r₀, hr₀, Hr₀⟩ := HA q hq
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min r₀ (1 / (4 * Real.sqrt 3 * K)), lt_min hr₀ (by positivity), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hann := restartRadialCurve_annulus hr.1 hρ hL hθ hζ
  have H := Hr₀ r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ (restartRadialCurve θ ζ ρ) hann.1
    (by linarith only [hann.2])
  have hρpos : 0 < ρ := hr.1.trans_le hρ.1
  have hζρ : 0 ≤ ζ ∧ ζ ≤ ρ / 9 := ⟨hζ.1, hζ.2.trans (by linarith only [hρ.1])⟩
  have HD := restartFastRadialPhase_derivative hhsmall hL hθ hρpos hζρ
    (mul_nonneg hA.le hr.1.le) H.2.1 H.2.2.2
  have Href := restartReferenceRadialPhase_curve_derivative hhsmall hL hθ hρpos hζρ
  have Herr : |deriv (restartFastRadialPhase h (q / 2 * Real.log (1 / r)) θ ζ) ρ -
      deriv (fun x => restartReferenceRadialPhase h (restartRadialCurve θ ζ x)) ρ| ≤ K * r := by
    calc
      _ ≤ (A * r) * (L + 1) := HD.2
      _ = K * r := by dsimp only [K]; ring
  have hKr : K * r ≤ 1 / (4 * Real.sqrt 3) := by
    have HB := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp
      (hr.2.trans (min_le_right _ _))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [HB]
  have hlower := (abs_le.mp Herr).1
  have hupper := (abs_le.mp Herr).2
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨H.1, HD.1, ?_, Herr, ?_, ?_⟩
  · exact H.2.2.1.trans (mul_le_mul_of_nonneg_right hAK (sq_nonneg r))
  · have Heq : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [Heq] at Href
    linarith only [hlower, Href.2.1, hKr]
  · linarith only [hupper, Href.2.2, hKr, hquarter]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartReferenceRadialPhase_curve_bounds {h r ρ θ ζ L : ℝ}
    (hh : 0 ≤ h ∧ h ≤ 1 / 16) (hr : 0 < r) (hρ : ρ ∈ Icc r (2 * r))
    (hL : 0 ≤ L) (hθ : |θ| ≤ L) (hζ : 0 ≤ ζ ∧ ζ ≤ r / 9) :
    r / 8 ≤ restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ) ∧
      restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ) ≤ 8 * (L + 1) * r := by
  let Z := restartRadialCurve θ ζ ρ
  have hnorm := (restartRadialCurve_annulus hr hρ hL hθ hζ).1
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrtSq, hsqrt]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrtSq, hsqrt]
  have hv : |Z 1 - Z 2| ≤ 2 * ‖Z‖ := by
    calc
      _ ≤ |Z 1| + |Z 2| := by simpa using abs_sub_le (Z 1) 0 (Z 2)
      _ ≤ ‖Z‖ + ‖Z‖ := add_le_add (norm_le_pi_norm Z 1) (norm_le_pi_norm Z 2)
      _ = _ := by ring
  have Hupper := sqrt_restartQuadratic_le_radius hh (norm_nonneg Z) (norm_le_pi_norm Z 0) hv
  have Hlower : r / 2 ≤ Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) := by
    obtain ⟨_, _, hc, _, _, _⟩ := restart_coefficients_small hh
    have hdiff : r / 2 ≤ ρ - ζ := by linarith only [hρ.1, hζ.2, hr]
    have hcv : r / 2 ≤ restartWallFactor h * (ρ - ζ) := by
      have H := mul_le_mul_of_nonneg_right hc (by linarith only [hdiff, hr] : 0 ≤ ρ - ζ)
      nlinarith only [H, hdiff]
    have H := Real.sqrt_le_sqrt (le_add_of_nonneg_left
      (sq_nonneg (restartShearFactor h * (θ * ρ) + restartShearCoupling h * (ρ - ζ))) :
      (restartWallFactor h * (ρ - ζ)) ^ 2 ≤ restartQuadratic h (θ * ρ) (ρ - ζ))
    rw [Real.sqrt_sq (by linarith only [hcv, hr])] at H
    exact hcv.trans H
  change r / 8 ≤ Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) / Real.sqrt 3 ∧
    Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) / Real.sqrt 3 ≤ 8 * (L + 1) * r
  constructor
  · apply (le_div_iff₀ hsqrt).mpr
    have H := mul_le_mul_of_nonneg_left hsqrt2 hr.le
    linarith only [Hlower, H, hr]
  · apply (div_le_iff₀ hsqrt).mpr
    have H := mul_le_mul_of_nonneg_left hsqrt1 (show 0 ≤ 8 * (L + 1) * r by positivity)
    nlinarith only [Hupper, hnorm, H]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartProjectionPhase_state_eq (h T θ ζ ρ : ℝ) :
    restartProjectionPhase (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)) =
      restartFastProjectionError h T θ ζ ρ + restartFastRadialPhase h T θ ζ ρ := by
  change restartProjectionPhase _ =
    (restartProjectionPhase _ - restartRadialPhase _) + restartRadialPhase _
  exact (sub_add_cancel _ _).symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartFastProjectionPhase_approximation :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let x := normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            0 < 1 + x 0 ∧
            DifferentiableAt ℝ (restartFastProjectionPhase h T θ ζ) ρ ∧
            |restartFastProjectionPhase h T θ ζ ρ -
              restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ)| ≤ K * r ^ 2 ∧
            |deriv (restartFastProjectionPhase h T θ ζ) ρ -
              deriv (fun y => restartReferenceRadialPhase h (restartRadialCurve θ ζ y)) ρ| ≤ K * r ∧
            1 / (4 * Real.sqrt 3) ≤ deriv (restartFastProjectionPhase h T θ ζ) ρ ∧
            deriv (restartFastProjectionPhase h T θ ζ) ρ ≤ (2 * L + 3) / Real.sqrt 3 + 1 := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartFastProjectionError_bounds
  obtain ⟨hR, hhR, HR⟩ := exists_restartFastRadialPhase_monotone
  refine ⟨min hE (min hR (1 / 16)), lt_min hhE (lt_min hhR (by norm_num)), ?_⟩
  intro h hh L hL
  obtain ⟨KE, hKE, HKE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨KR, hKR, HKR⟩ := HR h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL
  have hhsmall : 0 ≤ h ∧ h ≤ 1 / 16 :=
    ⟨hh.1.le, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩
  let K := KE + KR
  have hK : 0 < K := add_pos hKE hKR
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨rE, hrE, HrE⟩ := HKE q hq
  obtain ⟨rR, hrR, HrR⟩ := HKR q hq
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min rE (min rR (min (1 / 9) (1 / (4 * Real.sqrt 3 * K)))),
    lt_min hrE (lt_min hrR (lt_min (by norm_num) (by positivity))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrsmall : r ≤ 1 / 9 := ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrK : r ≤ 1 / (4 * Real.sqrt 3 * K) :=
    ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hζsmall : 0 ≤ ζ ∧ ζ ≤ r / 9 := ⟨hζ.1, hζ.2.trans (by nlinarith only [hr.1, hrsmall])⟩
  let T := q / 2 * Real.log (1 / r)
  obtain ⟨Hdom, HED, HEval, HEder, Hheight, Hgerm⟩ :=
    HrE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨_, HRD, HRval, HRder, _, _⟩ :=
    HrR r ⟨hr.1, (hr.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ θ ζ hθ hζsmall ρ hρ
  have Hlocal : restartFastProjectionPhase h T θ ζ =ᶠ[𝓝 ρ]
      (fun y => restartFastProjectionError h T θ ζ y + restartFastRadialPhase h T θ ζ y) := by
    filter_upwards [Hgerm] with y hy
    exact hy.trans (restartProjectionPhase_state_eq h T θ ζ y)
  have Hsum : HasDerivAt (restartFastProjectionPhase h T θ ζ)
      (deriv (restartFastProjectionError h T θ ζ) ρ + deriv (restartFastRadialPhase h T θ ζ) ρ) ρ := by
    convert! (HED.hasDerivAt.add HRD.hasDerivAt).congr_of_eventuallyEq Hlocal using 1
  have Hval : |restartFastProjectionPhase h T θ ζ ρ -
      restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ)| ≤ K * r ^ 2 := by
    rw [Hlocal.eq_of_nhds, add_sub_assoc]
    calc
      _ ≤ |restartFastProjectionError h T θ ζ ρ| +
          |restartFastRadialPhase h T θ ζ ρ - restartReferenceRadialPhase h (restartRadialCurve θ ζ ρ)| := abs_add_le _ _
      _ ≤ KE * r ^ 2 + KR * r ^ 2 := add_le_add HEval HRval
      _ = K * r ^ 2 := by dsimp only [K]; ring
  have Hder : |deriv (restartFastProjectionPhase h T θ ζ) ρ -
      deriv (fun y => restartReferenceRadialPhase h (restartRadialCurve θ ζ y)) ρ| ≤ K * r := by
    rw [Hsum.deriv, add_sub_assoc]
    calc
      _ ≤ |deriv (restartFastProjectionError h T θ ζ) ρ| +
          |deriv (restartFastRadialPhase h T θ ζ) ρ -
            deriv (fun y => restartReferenceRadialPhase h (restartRadialCurve θ ζ y)) ρ| := abs_add_le _ _
      _ ≤ KE * r + KR * r := add_le_add HEder HRder
      _ = K * r := by dsimp only [K]; ring
  have Href := restartReferenceRadialPhase_curve_derivative hhsmall hL hθ (hr.1.trans_le hρ.1)
    ⟨hζ.1, hζsmall.2.trans (by linarith only [hρ.1])⟩
  have hKr : K * r ≤ 1 / (4 * Real.sqrt 3) := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp hrK
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [H]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨Hdom, Hheight, Hsum.differentiableAt, Hval, Hder, ?_, ?_⟩
  · have heq : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [heq] at Href
    linarith only [(abs_le.mp Hder).1, Href.2.1, hKr]
  · linarith only [(abs_le.mp Hder).2, Href.2.2, hKr, hquarter]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastCoreRadius_eq_reciprocal (h T θ ζ ρ : ℝ) :
    restartFastCoreRadius h T θ ζ ρ = 2 / restartFastProjectionPhase h T θ ζ ρ := by
  simp [restartFastCoreRadius, restartFastProjectionPhase]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartFastCoreRadius_bounds :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let B := 8 * (L + 1) + 1
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastCoreRadius h T θ ζ) ρ ∧
            6 ≤ restartFastCoreRadius h T θ ζ ρ ∧
            2 / (B * r) ≤ restartFastCoreRadius h T θ ζ ρ ∧
            restartFastCoreRadius h T θ ζ ρ ≤ 32 / r ∧
            1 / (4 * B ^ 2 * r ^ 2) ≤ -deriv (restartFastCoreRadius h T θ ζ) ρ ∧
            -deriv (restartFastCoreRadius h T θ ζ) ρ ≤ 512 * (2 * L + 4) / r ^ 2 := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartFastProjectionPhase_approximation
  refine ⟨min hstar (1 / 16), lt_min hhstar (by norm_num), ?_⟩
  intro h hh L hL q hq
  obtain ⟨K, hK, HK⟩ := HH h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨rA, hrA, HA⟩ := HK q hq
  let B := 8 * (L + 1) + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨min rA (min (1 / 9) (min (1 / (16 * K)) (1 / (3 * B)))),
    lt_min hrA (lt_min (by norm_num) (lt_min (by positivity) (by positivity))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hr9 : r ≤ 1 / 9 := (hr.2.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrK : r ≤ 1 / (16 * K) :=
    ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrB : r ≤ 1 / (3 * B) :=
    ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hKr : K * r ≤ 1 / 16 := by
    have H := (le_div_iff₀ (by positivity : 0 < 16 * K)).mp hrK
    linarith only [H]
  have herr : K * r ^ 2 ≤ r / 16 := by
    nlinarith only [mul_le_mul_of_nonneg_right hKr hr.1.le]
  let T := q / 2 * Real.log (1 / r)
  obtain ⟨Hdom, _, HD, Hval, _, Hdl, Hdu⟩ :=
    HA r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨Hreflo, Hrefhi⟩ := restartReferenceRadialPhase_curve_bounds
    ⟨hh.1.le, hh.2.trans (min_le_right _ _)⟩ hr.1 hρ hL hθ
    ⟨hζ.1, hζ.2.trans (by nlinarith only [hr.1, hr9])⟩
  have Hlo : r / 16 ≤ restartFastProjectionPhase h T θ ζ ρ := by
    linarith only [(abs_le.mp Hval).1, Hreflo, herr]
  have Hhi : restartFastProjectionPhase h T θ ζ ρ ≤ B * r := by
    dsimp only [B]
    nlinarith only [(abs_le.mp Hval).2, Hrefhi, herr, hr.1]
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrtSq, hsqrt]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrtSq, hsqrt]
  have Hdlo : 1 / 8 ≤ deriv (restartFastProjectionPhase h T θ ζ) ρ := by
    apply le_trans _ Hdl
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    linarith only [hsqrt2]
  have Hdhi : deriv (restartFastProjectionPhase h T θ ζ) ρ ≤ 2 * L + 4 := by
    have H : (2 * L + 3) / Real.sqrt 3 ≤ 2 * L + 3 := by
      apply (div_le_iff₀ hsqrt).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hsqrt1 (by positivity : 0 ≤ 2 * L + 3)]
    linarith only [Hdu, H]
  obtain ⟨HKD, HKlo, HKhi, HKdlo, HKdhi⟩ :=
    reciprocal_radial_bounds hr.1 (show 0 ≤ 2 * L + 4 by positivity) HD Hlo Hhi Hdlo Hdhi
  have Heq : restartFastCoreRadius h T θ ζ = fun y => 2 / restartFastProjectionPhase h T θ ζ y :=
    funext (restartFastCoreRadius_eq_reciprocal h T θ ζ)
  have Hsix : 6 ≤ 2 / (B * r) := by
    apply (le_div_iff₀ (mul_pos hB hr.1)).mpr
    have H := (le_div_iff₀ (by positivity : 0 < 3 * B)).mp hrB
    nlinarith only [H]
  change _ ∧ DifferentiableAt ℝ (restartFastCoreRadius h T θ ζ) ρ ∧ _
  rw [Heq]
  exact ⟨Hdom, HKD, Hsix.trans HKlo, HKlo, HKhi, HKdlo, HKdhi⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartPartialCore_entry :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∀ ε ∈ Ioc (0 : ℝ) (1 / 10000), ∃ rstar : ℝ, 0 < rstar ∧
          ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) →
            ∀ ρ ∈ Icc r (2 * r),
              let T := q / 2 * Real.log (1 / r)
              let y := restartFastProjectiveEntry h T θ ζ ρ
              let k := restartFastCoreRadius h T θ ζ ρ
              let z := restartFastCoreAngle h T θ ζ ρ
              let Z := Real.arsinh (4 * (8 * (L + 1)))
              0 ≤ T ∧ 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ) ∧
              T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
              0 < restartFastProjectionHeight h T θ ζ ρ ∧
              max 6 (2 * Real.cosh Z) ≤ k ∧ z ∈ Icc (-Real.arcosh k) Z ∧
              toCoreAngleState y 0 = k ∧ 0 < y 1 ∧ 0 ≤ y 2 * y 3 ∧
              y 1 + y 2 * y 3 ≤ ε / k ∧ 2 ≤ y 2 ∧
              fromCoreAngleState z (toCoreAngleState y) = y ∧ coreRegion k y := by
  obtain ⟨hK, hhK, HK⟩ := exists_restartFastCoreRadius_bounds
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  refine ⟨min hK (min hV (1 / 16)), lt_min hhK (lt_min hhV (by norm_num)), ?_⟩
  intro h hh L hL q P hq hP ε hε
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rK, hrK, HRK⟩ := HK h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q hq2
  obtain ⟨rV, hrV, HRV⟩ := HV h
    ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL q hq2
  let M := 8 * (L + 1)
  let B := M + 1
  let Z := Real.arsinh (4 * M)
  have hM : 0 < M := by dsimp only [M]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hcosh : 0 < Real.cosh Z := Real.cosh_pos _
  obtain ⟨rB, hrB, HRB⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_core_budget (h := h) (M := M) hq hP hε.1)
  refine ⟨min rK (min rV (min rB (min (1 / 9)
    (min (1 / (32 * (L + 1))) (1 / (B * Real.cosh Z)))))),
    lt_min hrK (lt_min hrV (lt_min hrB (lt_min (by norm_num)
      (lt_min (by positivity) (by positivity))))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrV' := (hr.2.trans (min_le_right _ _))
  have hrB' := (hrV'.trans (min_le_right _ _))
  have hr9' := (hrB'.trans (min_le_right _ _))
  have hrL' := (hr9'.trans (min_le_right _ _))
  have hr9 : r ≤ 1 / 9 := hr9'.trans (min_le_left _ _)
  have hrL : r ≤ 1 / (32 * (L + 1)) := hrL'.trans (min_le_left _ _)
  have hrZ : r ≤ 1 / (B * Real.cosh Z) := hrL'.trans (min_le_right _ _)
  have hr1 : r ≤ 1 := hr9.trans (by norm_num)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1
      (by linarith only [hP] : (2 : ℝ) ≤ P)
  have hnorm := (restartRadialCurve_annulus hr.1 hρ hL hθ
    ⟨hζ2.1, hζ2.2.trans (by nlinarith only [hr.1, hr9])⟩).1
  have hsmall : ‖restartRadialCurve θ ζ ρ‖ ≤ 1 / 16 := by
    have H := (le_div_iff₀ (by positivity : 0 < 32 * (L + 1))).mp hrL
    linarith only [hnorm, H]
  have hhsmall : |h| ≤ 1 / 16 := by
    rw [abs_of_pos hh.1]
    exact ((hh.2.trans (min_le_right _ _)).trans (min_le_right _ _))
  have hrad := restartSectionRadicand_pos_of_small hhsmall hsmall
  let T := q / 2 * Real.log (1 / r)
  let y := restartFastProjectiveEntry h T θ ζ ρ
  let k := restartFastCoreRadius h T θ ζ ρ
  let z := restartFastCoreAngle h T θ ζ ρ
  have hT : 0 ≤ T := by
    dsimp only [T]
    apply mul_nonneg (by linarith only [hq])
    apply Real.log_nonneg
    exact (le_div_iff₀ hr.1).mpr (by simpa using hr1)
  obtain ⟨Hdom, _, hk6, hklo, hkhi, _, _⟩ :=
    HRK r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨_, _, _, _, hAlo, _, _, hv2, _, _, hu, _, hp, hz⟩ :=
    HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  change 6 ≤ k at hk6
  change 2 / (B * r) ≤ k at hklo
  change k ≤ 32 / r at hkhi
  change 2 ≤ y 2 at hv2
  change 0 < y 1 ∧ y 1 ≤ 32 * h * r ^ (q - 2) at hu
  change 0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 2048 * M * ζ / r ^ 3 at hp
  change |z| ≤ Z at hz
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk6
  have hkZ : 2 * Real.cosh Z ≤ k := by
    apply le_trans _ hklo
    apply (le_div_iff₀ (mul_pos hB hr.1)).mpr
    have H := (le_div_iff₀ (mul_pos hB hcosh)).mp hrZ
    nlinarith only [H]
  have Hbudget := HRB ⟨hr.1, hrB'.trans (min_le_left _ _)⟩
  have Hsmall : y 1 + y 2 * y 3 ≤ ε / k :=
    restart_core_amplitude_budget hr.1 hM.le hk0 hkhi ⟨hu.1.le, hu.2⟩ hp hζ.2 Hbudget
  have hv1 : 1 ≤ y 2 := le_trans (by norm_num) hv2
  have Hangle : -Real.arcosh k ≤ z :=
    (abs_le.mp (coreAngle_abs_le_arcosh hv1)).1
  have Hregion : coreRegion k y := partialCoreEntry_region hk6 hv1 hu.1.le hp.1 hε.2 Hsmall
  exact ⟨hT, hrad, Hdom, lt_of_lt_of_le (by positivity [hr.1]) hAlo,
    max_le hk6 hkZ, ⟨Hangle, (abs_le.mp hz).2⟩, rfl, hu.1, hp.1, Hsmall, hv2,
    fromCoreAngleState_toCoreAngleState (zero_lt_one.trans_le hv1), Hregion⟩

end
end

private theorem BianchiIX.contDiffAt_restartFastProjectiveEntry_joint {h s θ ζ ρ : ℝ}
    (hZ : 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hs : s ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0)
    (hA : restartFastProjectionHeight h s θ ζ ρ ≠ 0) :
    ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartFastProjectiveEntry h s p.1.1 p.1.2 p.2)
      ((θ, ζ), ρ) := by
  have hc : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartRadialCurve p.1.1 p.1.2 p.2) ((θ, ζ), ρ) := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [restartRadialCurve] <;> fun_prop
  have hchart := (contDiffAt_restartSectionChart hZ 2).comp ((θ, ζ), ρ) hc
  have hflow := (contDiffAt_normalizedMaxCurve_two hs).comp ((θ, ζ), ρ)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (hchart.prodMk (contDiffAt_const (c := s)))
  exact (contDiffAt_toProjectiveState 2 hA).comp ((θ, ζ), ρ) hflow

/-- The canonical restart is jointly C2 in the two labels and the ordinary radial coordinate. -/
theorem solution :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartFastProjectiveEntry h s p.1.1 p.1.2 p.2) ((θ, ζ), ρ) ∧
              ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnParameters h s p.1.1 p.1.2 p.2) ((θ, ζ), ρ) ∧
              ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnState h s p.1.1 p.1.2 p.2) ((θ, ζ), ρ) ∧
              ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnPhase h s p.1.1 p.1.2 p.2) ((θ, ζ), ρ) ∧
              ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnTime h s p.1.1 p.1.2 p.2) ((θ, ζ), ρ) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_entry
  obtain ⟨hC, hhC, HC⟩ := exists_restartPartialCore_connection
  refine ⟨min hE hC, lt_min hhE hhC, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rE, hrE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨rC, hrC, HRC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min rE rC, lt_min hrE hrC, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  obtain ⟨_, hrad, hdom, hA, hk, _, hR, _, _, _, hV, _, hy⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ ⟨hζ.1.le, hζ.2⟩ ρ hρ
  obtain ⟨T, _, hfirst, _, _, hμ, hu, hw, _, _, hphase, _, hct, _⟩ :=
    HRC r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩ θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let base : (ℝ × ℝ) × ℝ := ((θ, ζ), ρ)
  let Y := fun p : (ℝ × ℝ) × ℝ => restartFastProjectiveEntry h s p.1.1 p.1.2 p.2
  have hcY : ContDiffAt ℝ 2 Y base := contDiffAt_restartFastProjectiveEntry_joint hrad hdom hA.ne'
  have Hcore := partialCoreReturn_regular ((le_max_left _ _).trans hk) hy hR
    (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hV)
  have ht : partialCoreReturnTime (Y base) = T := Hcore.1.unique hfirst
  have hZeq : partialCoreReturnState (Y base) = toCoreAngleState (projectiveOriginalFlow (Y base) 0 T) := by
    simp only [partialCoreReturnState, ht]
  have hp : restartReturnParameters h s θ ζ ρ =
      coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow (Y base) 0 T)) :=
    congrArg coreExitConnectionParameters hZeq
  have hZlo : 1 < partialCoreReturnState (Y base) 0 := by
    have H := phaseNorm_ge (b := 1) (show 0 ≤ coreExitConnectionParameters
      (toCoreAngleState (projectiveOriginalFlow (Y base) 0 T)) 0 + 1 by linarith only [hμ.1])
    rw [hphase] at H
    rw [hZeq]
    change 1 < coreRadius (projectiveOriginalFlow (Y base) 0 T 0) (projectiveOriginalFlow (Y base) 0 T 2)
    linarith only [hμ.1, H]
  have hcZ := Hcore.2.2.1.comp base hcY
  have hcp : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnParameters h s p.1.1 p.1.2 p.2) base :=
    (contDiffAt_coreExitConnectionParameters 2 hZlo).comp base hcZ
  have hcG : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnState h s p.1.1 p.1.2 p.2) base := by
    apply ContDiffAt.comp (g := connectionReturnPhysicalState) base _ hcp
    change ContDiffAt ℝ 2 connectionReturnPhysicalState (restartReturnParameters h s θ ζ ρ)
    rw [hp]
    exact contDiffAt_connectionReturnPhysicalState hμ.1 ⟨hu.1.le, hu.2⟩ hw
  have hg0 : restartReturnState h s θ ζ ρ 0 ≠ 0 := by
    change phaseNorm (-connectionReturnState (restartReturnParameters h s θ ζ ρ) 0 - 1) 1 ≠ 0
    exact ne_of_gt (by unfold phaseNorm; positivity)
  have hcphase : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnPhase h s p.1.1 p.1.2 p.2) base :=
    contDiffAt_const.div (contDiffAt_pi.mp hcG 0) hg0
  have hctime : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnTime h s p.1.1 p.1.2 p.2) base := by
    apply (contDiffAt_const.add (Hcore.2.1.comp base hcY)).add
    apply ContDiffAt.comp (g := connectionReturnTime) base _ hcp
    change ContDiffAt ℝ 2 connectionReturnTime (restartReturnParameters h s θ ζ ρ)
    rw [hp]
    exact hct
  exact ⟨hcY, hcp, hcG, hcphase, hctime⟩
