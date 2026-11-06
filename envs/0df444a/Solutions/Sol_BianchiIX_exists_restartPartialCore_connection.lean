-- Prove2me | solution 1 for BianchiIX.exists_restartPartialCore_connection
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:48:55.180472+00:00
-- url     : https://prove2.me/submissions/d070379e-876a-4392-a755-3338e8ce26f7

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
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
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreClockProjection_growth
import Theorems.Thm_BianchiIX_exists_normalized_partialCore_return
import Theorems.Thm_BianchiIX_exists_restartFastProjectionError_bounds
import Theorems.Thm_BianchiIX_exists_restartFastProjectiveEntry_bounds
import Theorems.Thm_BianchiIX_exists_restartSection_radial_approximation
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_core_prefix_contraction
import Theorems.Thm_BianchiIX_normalized_core_residence
import Theorems.Thm_BianchiIX_normalized_core_return_downward
import Theorems.Thm_BianchiIX_normalized_core_return_isLeast
import Theorems.Thm_BianchiIX_normalized_partialCore_energy_band_improves
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_partialCore_field_bounds
import Theorems.Thm_BianchiIX_projectiveOriginalFlow_restart
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_reciprocal_radial_bounds
import Theorems.Thm_BianchiIX_sech_le_exp
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Positivity
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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.core_exit_connection_radial_range {k m : ℝ} (hk : 6 ≤ k) (hm : m < 1)
    (hE : |coreEnergy m 1 - k ^ 2| ≤ 1 / 8) : 4 ≤ -m ∧ k / 2 ≤ -m ∧ -m < k := by
  have hElo := (abs_le.mp hE).1
  have hEhi := (abs_le.mp hE).2
  dsimp [coreEnergy] at hElo hEhi
  have hm4 : 4 ≤ -m := by
    by_contra H
    have hm5 : 1 - m < 5 := by linarith only [H]
    have hs : (1 - m) ^ 2 < 5 ^ 2 :=
      (sq_lt_sq₀ (by linarith only [hm] : 0 ≤ 1 - m) (by norm_num)).mpr hm5
    nlinarith only [hs, hElo, hk, sq_nonneg (k - 6)]
  refine ⟨hm4, ?_, ?_⟩
  · by_contra H
    have hs : (1 - m) ^ 2 < (k / 2 + 1) ^ 2 :=
      (sq_lt_sq₀ (by linarith only [hm] : 0 ≤ 1 - m) (by linarith only [hk])).mpr (by linarith only [H])
    nlinarith only [hs, hElo, hk, sq_nonneg (k - 6)]
  · by_contra H
    have hs : k ^ 2 ≤ (-m) ^ 2 := (sq_le_sq₀ (by linarith only [hk]) (by linarith only [hm4])).mpr (by linarith only [H])
    nlinarith only [hs, hEhi, hm4]

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
open Set Filter
open scoped Topology

private theorem BianchiIX.toProjectiveState_wall_sign {x : NormalizedState} (hA : 0 < 1 + x 0) (i : Fin 3) :
    (toProjectiveState x i.succ = 0 ↔ wallValue i x = 0) ∧
      (0 ≤ toProjectiveState x i.succ ↔ 0 ≤ wallValue i x) := by
  have heq : toProjectiveState x i.succ = Real.sqrt 3 * wallValue i x / (1 + x 0) := by
    fin_cases i <;> rfl
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [heq]
  constructor
  · simp only [div_eq_zero_iff, mul_eq_zero, ne_of_gt hsqrt, ne_of_gt hA, false_or, or_false]
  · rw [div_eq_mul_inv, mul_nonneg_iff_of_pos_right (inv_pos.mpr hA), mul_nonneg_iff_of_pos_left hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_projective_wall_sign {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (β t i.succ = 0 ↔ β s i.succ = 0) ∧ (0 ≤ β t i.succ ↔ 0 ≤ β s i.succ) := by
  have H := normalized_wall_sign (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
    (fun _ hh => hasDerivAt_normalizedMaxCurve hh) hs ht i
  exact ⟨(toProjectiveState_wall_sign hAt i).1.trans (H.1.trans (toProjectiveState_wall_sign hAs i).1.symm),
    (toProjectiveState_wall_sign hAt i).2.trans (H.2.trans (toProjectiveState_wall_sign hAs i).2.symm)⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_projective_wall_pos {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) (hi : 0 < toProjectiveState (normalizedMaxCurve x t₀ s) i.succ) :
    0 < toProjectiveState (normalizedMaxCurve x t₀ t) i.succ := by
  have H := normalized_projective_wall_sign hs ht hAs hAt i
  have hne : toProjectiveState (normalizedMaxCurve x t₀ t) i.succ ≠ 0 :=
    fun h => (ne_of_gt hi) (H.1.mp h)
  exact lt_of_le_of_ne (H.2.mpr hi.le) hne.symm

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

private theorem BianchiIX.coreExitConnectionParameters_phase {Z : CoreAngleState} (hK : 1 < Z 0) :
    phaseNorm (coreExitConnectionParameters Z 0 + 1) 1 = Z 0 := by
  have hs := Real.sq_sqrt (by nlinarith only [hK] : 0 ≤ Z 0 ^ 2 - 1)
  change Real.sqrt ((Real.sqrt (Z 0 ^ 2 - 1) - 1 + 1) ^ 2 + 1 ^ 2) = Z 0
  rw [show (Real.sqrt (Z 0 ^ 2 - 1) - 1 + 1) ^ 2 + 1 ^ 2 = Z 0 ^ 2 by nlinarith only [hs]]
  exact Real.sqrt_sq (by linarith only [hK])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreExitConnectionParameters_of_exit {y : ProjectiveState} (hM : y 0 < 1) (hV : y 2 = 1) :
    coreExitConnectionParameters (toCoreAngleState y) = ![-y 0, y 1, y 3] := by
  have hs : (toCoreAngleState y 0) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    change coreRadius (y 0) (y 2) ^ 2 - 1 = _
    rw [coreRadius_sq, hV]
    dsimp [coreEnergy]
    ring
  ext i
  fin_cases i
  · change Real.sqrt ((toCoreAngleState y 0) ^ 2 - 1) - 1 = -y 0
    rw [hs, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hM] : y 0 - 1 < 0)]
    ring
  · rfl
  · change y 2 * y 3 = y 3
    rw [hV, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCore_firstReturn_connection_domain {k Z T ε : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hz : projectiveCoreAngle y ≤ Z) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < y 1 ∧ y 1 ≤ ε / k) (hp : 0 < y 2 * y 3 ∧ y 2 * y 3 ≤ ε / k)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T) :
    let out := projectiveOriginalFlow y 0 T
    let p := coreExitConnectionParameters (toCoreAngleState out)
    out = connectionEntry (p 0) (p 1) (p 2) ∧
      (4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k) ∧
      (0 < p 1 ∧ p 1 ≤ ε / p 0) ∧ (0 < p 2 ∧ p 2 ≤ ε) ∧
      p 1 ≤ y 1 * Real.exp (-k / 12) ∧ p 2 ≤ y 2 * y 3 ∧
      phaseNorm (p 0 + 1) 1 = coreRadius (out 0) (out 2) ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 T 0 ∧
      connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
      ContDiffAt ℝ 2 connectionReturnState p := by
  intro out p
  have hk0 : 0 < k := by linarith only [hk]
  obtain ⟨S, _, hfirstS, hreg, _⟩ := exists_partialCore_entry_variation hk hy hR hV
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hreg
  have htm : T ∈ Icc 0 T := ⟨hfirst.1.1.le, le_rfl⟩
  have hr : coreRegion k out := (hreg T htm).2
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have hhit : out 2 = 1 := hfirst.1.2
  have hdown := normalized_core_return_downward hc hk le_rfl hfirst.1.1 (hreg T htm).1 hhit
    (fun t ht => (hreg t ⟨ht.1.le, ht.2.le⟩).2.2.1)
    (coreRegion_radius_bounds hk hr).1 (coreRegion_wall_bounds hr).1 (coreRegion_wall_bounds hr).2
  have hM : out 0 < 1 := hdown.1
  have heq : p = ![-out 0, out 1, out 3] := coreExitConnectionParameters_of_exit hM hhit
  have hμ := core_exit_connection_radial_range hk hM (by simpa only [hhit] using hr.1)
  have hentry : out = connectionEntry (p 0) (p 1) (p 2) := by
    rw [heq]
    ext i
    fin_cases i <;> simp [connectionEntry, hhit]
  have hpos (i : Fin 3) (hi : 0 < y i.succ) : 0 < out i.succ := by
    apply normalized_projective_wall_pos (initial_mem_normalizedMaxDomain _ 0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hfirst.1.1.le)
      (hreg 0 ⟨le_rfl, hfirst.1.1.le⟩).1 (hreg T htm).1 i
    change 0 < projectiveOriginalFlow y 0 0 i.succ
    rw [projectiveOriginalFlow_initial hD]
    exact hi
  have huout : 0 < out 1 := hpos 0 hu.1
  have hpout : 0 < out 3 := hpos 2 ((mul_pos_iff_of_pos_left (zero_lt_one.trans hV)).mp hp.1)
  have HC := partialCore_firstReturn_contraction hk hy hR hV hZ hkZ hz hfirst
  have huexp : y 1 * Real.exp (-k / 12) ≤ y 1 :=
    mul_le_of_le_one_right hu.1.le (Real.exp_le_one_iff.mpr (by linarith only [hk]))
  have hdomainU : 0 < p 1 ∧ p 1 ≤ ε / p 0 := by
    change 0 < out 1 ∧ out 1 ≤ ε / (p 0)
    refine ⟨huout, (HC.1.trans huexp).trans (hu.2.trans ?_)⟩
    rw [heq]
    exact div_le_div_of_nonneg_left hε.1.le (by simpa using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hμ.1) hμ.2.2.le
  have hdomainP : 0 < p 2 ∧ p 2 ≤ ε := by
    change 0 < out 2 * out 3 ∧ out 2 * out 3 ≤ ε
    rw [hhit, one_mul]
    exact ⟨hpout, HC.2.trans (hp.2.trans (div_le_self hε.1.le (by linarith only [hk])))⟩
  have hμp : 4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k := by simpa only [heq, Matrix.cons_val_zero] using hμ
  have HR := connectionReturn_regular hμp.1
    ⟨hdomainU.1.le, hdomainU.2.trans (div_le_div_of_nonneg_right hε.2 (by linarith only [hμp.1]))⟩
    ⟨hdomainP.1, hdomainP.2.trans hε.2⟩
  refine ⟨hentry, hμp, hdomainU, hdomainP, ?_, ?_, ?_, (hreg T htm).1, HR.1, HR.2.1, HR.2.2.1⟩
  · exact HC.1
  · change out 2 * out 3 ≤ y 2 * y 3
    rw [hhit, one_mul]
    exact HC.2
  · apply coreExitConnectionParameters_phase
    exact lt_of_lt_of_le (by linarith only [hk] : 1 < 99 / 100 * k) (coreRegion_radius_bounds hk hr).1

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

/-- The positive weak-wall family reaches a regular long connection along the same Einstein orbit. -/
theorem solution :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∀ ε ∈ Ioc (0 : ℝ) (1 / 10000), ∃ rstar : ℝ, 0 < rstar ∧
          ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
            ∀ ρ ∈ Icc r (2 * r),
              let s := q / 2 * Real.log (1 / r)
              let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
              let y := restartFastProjectiveEntry h s θ ζ ρ
              let k := restartFastCoreRadius h s θ ζ ρ
              ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
                IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} (s + T) ∧
                let out := projectiveOriginalFlow y 0 T
                let p := coreExitConnectionParameters (toCoreAngleState out)
                out = connectionEntry (p 0) (p 1) (p 2) ∧
                (4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k) ∧
                (0 < p 1 ∧ p 1 ≤ ε / p 0) ∧ (0 < p 2 ∧ p 2 ≤ ε) ∧
                p 1 ≤ y 1 * Real.exp (-k / 12) ∧ p 2 ≤ y 2 * y 3 ∧
                phaseNorm (p 0 + 1) 1 = coreRadius (out 0) (out 2) ∧
                connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
                ContDiffAt ℝ 2 connectionReturnState p ∧
                connectionReturnState p = toProjectiveState
                  (normalizedMaxCurve x 0 (s + T + connectionReturnTime p)) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartPartialCore_entry
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP ε hε
  obtain ⟨rstar, hrstar, HR⟩ := HH h hh L hL q P hq hP ε hε
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
  let y := restartFastProjectiveEntry h s θ ζ ρ
  let k := restartFastCoreRadius h s θ ζ ρ
  let Z := Real.arsinh (4 * (8 * (L + 1)))
  obtain ⟨hs, hrad, _, hA, hk6, hz, hR, hu0, hp0, hsum, hV, _, hy⟩ :=
    HR r hr θ ζ hθ ⟨hζ.1.le, hζ.2⟩ ρ hρ
  have hk : 6 ≤ k := (le_max_left _ _).trans hk6
  have hc : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have hinit : positiveWalls x := ⟨hh.1, hr.1.trans_le hρ.1, hζ.1⟩
  have hpos := (normalizedMaxCurve_forward hinit hc hs).2.1
  have hwpos : 0 < y 3 := div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hpos.2.2) hA
  have hp : 0 < y 2 * y 3 := mul_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hV) hwpos
  have huε : y 1 ≤ ε / k := (le_add_of_nonneg_right hp0).trans hsum
  have hpε : y 2 * y 3 ≤ ε / k := (le_add_of_nonneg_left hu0.le).trans hsum
  have hV1 : 1 < y 2 := lt_of_lt_of_le (by norm_num) hV
  have hZ : 0 ≤ Z := Real.arsinh_nonneg_iff.mpr (by positivity)
  obtain ⟨T, hT, hfirst, _⟩ := exists_partialCore_entry_variation hk hy hR hV1
  let out := projectiveOriginalFlow y 0 T
  let p := coreExitConnectionParameters (toCoreAngleState out)
  obtain ⟨hentry, hμ, hu, hw, hdecU, hdecP, hphase, hAt, hvalid, hct, hcs⟩ :=
    partialCore_firstReturn_connection_domain hk hy hR hV1 hZ ((le_max_right _ _).trans hk6)
      hz.2 hε ⟨hu0, huε⟩ ⟨hp, hpε⟩ hfirst
  have htc : 0 < connectionReturnTime p := hvalid.1.1.1
  have hD := (coreRegion_clock_regular hk hy).1
  have Hrestart := projectiveOriginalFlow_restart hD hT.le htc.le hAt
  have Hconn : connectionReturnState p = projectiveOriginalFlow y 0 (T + connectionReturnTime p) := by
    change projectiveOriginalFlow (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) = _
    rw [← hentry]
    simpa only [add_comm (connectionReturnTime p) T] using Hrestart
  have Hfast := restartFastProjectiveEntry_flow hrad.le hs hA (add_nonneg hT.le htc.le)
  refine ⟨T, hT, hfirst, restartFastProjectiveEntry_firstReturn hrad.le hs hA hfirst,
    hentry, hμ, hu, hw, hdecU, hdecP, hphase, hvalid, hct, hcs, ?_⟩
  exact (Hconn.trans Hfast).trans (by rw [add_assoc])
