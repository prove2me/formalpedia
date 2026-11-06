-- Prove2me | solution 1 for BianchiIX.exists_restartConnection_output_phase
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:51:57.883926+00:00
-- url     : https://prove2.me/submissions/31dab541-9e4e-4c66-b2dc-225d72c872c8

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
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
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_Dynamics_CoreMultipliers
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturnValues
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Theorems.Thm_BianchiIX_connectionLog_matchingPhase_drift
import Theorems.Thm_BianchiIX_connectionLog_prefix_estimates
import Theorems.Thm_BianchiIX_connectionReturn_phase_response_bounds
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_connection_phase_radial_budget
import Theorems.Thm_BianchiIX_connection_reciprocal_radial_bounds
import Theorems.Thm_BianchiIX_contDiffAt_coreOriginalLogRates
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_moving_intervalIntegral_of_contDiffAt
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
import Theorems.Thm_BianchiIX_eventually_partialCore_multiplier_formula
import Theorems.Thm_BianchiIX_exists_connection_first_return
import Theorems.Thm_BianchiIX_exists_normalized_connection_log_segment
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_exists_normalized_partialCore_return
import Theorems.Thm_BianchiIX_exists_restartFastProjectionError_bounds
import Theorems.Thm_BianchiIX_exists_restartFastProjectiveEntry_bounds
import Theorems.Thm_BianchiIX_exists_restartPartialCore_connection
import Theorems.Thm_BianchiIX_exists_restartPartialCore_radial_data
import Theorems.Thm_BianchiIX_exists_restartSection_radial_approximation
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_mobius_radial_correction_bounds
import Theorems.Thm_BianchiIX_multiplier_radial_derivative
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_core_residence
import Theorems.Thm_BianchiIX_normalized_core_return_downward
import Theorems.Thm_BianchiIX_normalized_core_return_isLeast
import Theorems.Thm_BianchiIX_normalized_partialCore_energy_band_improves
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_partialCoreReturn_log_derivative_bounds
import Theorems.Thm_BianchiIX_partialCore_field_bounds
import Theorems.Thm_BianchiIX_partialCore_wall_arrival_radius_response
import Theorems.Thm_BianchiIX_partial_core_connection_wall_budget
import Theorems.Thm_BianchiIX_partial_core_radial_derivative_budget
import Theorems.Thm_BianchiIX_partial_core_radial_log_bounds
import Theorems.Thm_BianchiIX_partial_core_radial_variation_budget
import Theorems.Thm_BianchiIX_partial_core_reciprocal_radial_bounds
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
open Set Filter
open scoped Topology

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

private theorem BianchiIX.three_coordinate_expansion (v : Fin 3 → ℝ) :
    v = v 0 • ![1, 0, 0] + v 1 • ![0, 1, 0] + v 2 • ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.three_coordinate_linear_bound (A : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ) :
    |A v| ≤ |v 0| * |A ![1, 0, 0]| + |v 1| * |A ![0, 1, 0]| + |v 2| * |A ![0, 0, 1]| := by
  have hid : A v = v 0 * A ![1, 0, 0] + v 1 * A ![0, 1, 0] + v 2 * A ![0, 0, 1] := by
    conv_lhs => rw [three_coordinate_expansion v]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hid]
  simpa only [abs_mul] using
    (abs_add_le (v 0 * A ![1, 0, 0] + v 1 * A ![0, 1, 0]) (v 2 * A ![0, 0, 1])).trans
      (add_le_add (abs_add_le (v 0 * A ![1, 0, 0]) (v 1 * A ![0, 1, 0])) le_rfl)

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

private theorem BianchiIX.restart_entry_linear_amplitude_budget {r h M q P ζ U W : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hh : 0 ≤ h) (hM : 0 ≤ M) (hq : 3 < q) (hP : 4 < P)
    (hζ : 0 ≤ ζ ∧ ζ ≤ r ^ P)
    (hU : 0 ≤ U ∧ U ≤ 32 * h * r ^ (q - 2))
    (hW : 0 ≤ W ∧ W ≤ 2048 * M * ζ / r ^ 3) :
    U ≤ 32 * h * r ∧ W ≤ 2048 * M * r ∧ U + W ≤ (32 * h + 2048 * M) * r := by
  have hr0 := hr.1
  have hp1 : r ^ (q - 2) ≤ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2
      (by linarith only [hq] : (1 : ℝ) ≤ q - 2)
  have hp4 : ζ ≤ r ^ 4 := hζ.2.trans (by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2
      (by linarith only [hP] : (4 : ℝ) ≤ P))
  have HU : U ≤ 32 * h * r := hU.2.trans (mul_le_mul_of_nonneg_left hp1 (by positivity))
  have HW : W ≤ 2048 * M * r := hW.2.trans (calc
    _ ≤ 2048 * M * r ^ 4 / r ^ 3 := by gcongr
    _ = _ := by field_simp)
  exact ⟨HU, HW, (add_le_add HU HW).trans_eq (by ring)⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_denom_bound {m u v w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w ∧ 0 < projectiveDenom (-m) u v w := by
  have H : 3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w := by
    dsimp [projectiveDenom, curvature]
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu.1,
      mul_le_mul_of_nonneg_left hw.2 hu.1, sq_nonneg u, sq_nonneg (v - w)]
  exact ⟨H, by nlinarith only [H, hu.2, sq_nonneg m]⟩

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

private theorem BianchiIX.phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_defect {a b : ℝ} (ha : 0 < a) :
    phaseNorm a b - a = b ^ 2 / (phaseNorm a b + a) := by
  apply (eq_div_iff (ne_of_gt (add_pos (phaseNorm_pos ha) ha))).mpr
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ratio_bounds {a b : ℝ} (ha : 2 ≤ a) (hb : 0 ≤ b ∧ b ≤ 1) :
    7 / 8 ≤ a / phaseNorm a b ∧ a / phaseNorm a b ≤ 1 := by
  have ha0 : 0 < a := by linarith only [ha]
  have hn := phaseNorm_pos (b := b) ha0
  have hb2 : b ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hb.1 hb.2 2
  have ha2 : 4 ≤ a ^ 2 := by nlinarith only [ha, sq_nonneg (a - 2)]
  have hupper : phaseNorm a b ≤ 8 * a / 7 := by
    nlinarith only [phaseNorm_sq a b, hb2, ha2, hn, ha0]
  exact ⟨(le_div_iff₀ hn).mpr (by linarith only [hupper]),
    (div_le_one hn).mpr (phaseNorm_ge ha0.le)⟩

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

private theorem BianchiIX.phaseNorm_defect_bounds {μ a b : ℝ} (hμ : 0 < μ) (ha : μ / 2 ≤ a) :
    0 ≤ phaseNorm a b - a ∧ phaseNorm a b - a ≤ b ^ 2 / μ := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hnorm := phaseNorm_ge (b := b) ha0.le
  refine ⟨sub_nonneg.mpr hnorm, ?_⟩
  rw [phaseNorm_defect ha0]
  exact div_le_div_of_nonneg_left (sq_nonneg b) hμ (by linarith only [ha, hnorm])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.matchingPhase_endpoint_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hu : 0 ≤ u) (hv : 0 ≤ v ∧ v ≤ w)
    (hJ : |matchingPhase m v 1 - matchingPhase μ 1 w| ≤ 20 * u / μ + w ^ 2 / μ ^ 2) :
    |phaseNorm (m - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (u + w ^ 2) / μ := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have he0 := phaseNorm_defect_bounds (b := w) hμ0 (show μ / 2 ≤ μ - 1 by linarith only [hμ])
  have he1 := phaseNorm_defect_bounds (b := v) hμ0
    (show μ / 2 ≤ m + 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hv2 := pow_le_pow_left₀ hv.1 hv.2 2
  have he1' := he1.2.trans (div_le_div_of_nonneg_right hv2 hμ0.le)
  have hid : phaseNorm (m - 1) 1 - phaseNorm (μ + 1) 1 + 2 =
      matchingPhase m v 1 - matchingPhase μ 1 w +
        (phaseNorm (μ - 1) w - (μ - 1)) - (phaseNorm (m + 1) v - (m + 1)) := by
    dsimp [matchingPhase]
    ring
  rw [hid]
  have H := (abs_sub (matchingPhase m v 1 - matchingPhase μ 1 w + (phaseNorm (μ - 1) w - (μ - 1)))
    (phaseNorm (m + 1) v - (m + 1))).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_of_nonneg he0.1, abs_of_nonneg he1.1] at H
  apply (H.trans (add_le_add (add_le_add hJ he0.2) he1')).trans
  have hμsq : μ ≤ μ ^ 2 := by nlinarith only [hμ, sq_nonneg (μ - 1)]
  have hsq := div_le_div_of_nonneg_left (sq_nonneg w) hμ0 hμsq
  have huq := div_nonneg hu hμ0.le
  have hwq := div_nonneg (sq_nonneg w) hμ0.le
  calc
    20 * u / μ + w ^ 2 / μ ^ 2 + w ^ 2 / μ + w ^ 2 / μ ≤
        20 * (u / μ) + 3 * (w ^ 2 / μ) := by
      calc
        _ ≤ 20 * u / μ + w ^ 2 / μ + w ^ 2 / μ + w ^ 2 / μ := by gcongr
        _ = _ := by ring
    _ ≤ 24 * (u / μ) + 24 * (w ^ 2 / μ) := by nlinarith only [huq, hwq]
    _ = 24 * (u + w ^ 2) / μ := by ring

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

private theorem BianchiIX.connectionLog_endpoint_phase_bound {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hinit : -Y a 0 = μ) (hV : Y a 2 = 1) (hhit : Y b 3 = 1) :
    |phaseNorm (-Y b 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (Y a 1 + (Y a 3) ^ 2) / μ := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hentry : Y a 1 ≤ Y a 2 := by rw [hV]; linarith only [(hu a ha).2]
  have hp := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).2.2.2.1
  have hexp : Real.exp (-2 * (b - a) / μ) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr hab))
      (by linarith only [hμ])
  have hvw : Y b 2 ≤ Y a 3 := by
    rw [hV, hhit, mul_one, one_mul] at hp
    exact hp.trans ((mul_le_mul_of_nonneg_left hexp (hw a ha).1).trans_eq (mul_one _))
  have hJ := connectionLog_matchingPhase_drift hab hμ hY hm hu hv hw hentry
  rw [hinit, hV, hhit, one_mul] at hJ
  exact matchingPhase_endpoint_bound hμ (hm b hb) (hu a ha).1 ⟨(hv b hb).1.le, hvw⟩ hJ

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

private theorem BianchiIX.normalized_connection_endpoint_phase_bound {x : NormalizedState} {t₀ μ s t : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    (∀ u ∈ Icc s t, connectionRegion μ (β u)) → -β s 0 = μ → β s 2 = 1 →
    0 < β s 3 → β t 3 = 1 →
    |phaseNorm (-β t 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (β s 1 + (β s 3) ^ 2) / μ := by
  intro β hregion hinit hV hw hhit
  obtain ⟨hL, q, hq0, hqt, hqmap, _, hqode⟩ :=
    exists_normalized_connection_log_segment hc hμ hs hst hA hregion hw
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hdom (u : ℝ) (hu : u ∈ Icc s t) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  have hvpos (u : ℝ) (hu : u ∈ Icc s t) : 0 < β u 2 := by
    apply normalized_projective_wall_pos (hdom s hsm) (hdom u hu) (hA s hsm) (hA u hu) 1
    change 0 < β s 2
    rw [hV]
    norm_num
  have H := connectionLog_endpoint_phase_bound hL hμ hqode
    (fun z hz => (hregion _ (hqmap hz)).1)
    (fun z hz => (hregion _ (hqmap hz)).2.1)
    (fun z hz => ⟨hvpos _ (hqmap hz), (hregion _ (hqmap hz)).2.2.1.2⟩)
    (fun z hz => (hregion _ (hqmap hz)).2.2.2)
    (by change -β (q 0) 0 = μ; rwa [hq0])
    (by change β (q 0) 2 = 1; rwa [hq0])
    (by change β (q _) 3 = 1; rwa [hqt])
  simpa only [hq0, hqt] using H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_connection_phase_bound {μ u w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 < w ∧ w ≤ 1 / 10000) :
    let x := fromProjectiveState (connectionEntry μ u w)
    let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
    ∃ T > (0 : ℝ),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧ β t 3 = 1} T ∧
      (∀ t ∈ Icc 0 T, 3 / (2 * μ ^ 2) ≤ 1 + normalizedMaxCurve x 0 t 0 ∧ connectionRegion μ (β t)) ∧
      |phaseNorm (-β T 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (u + w ^ 2) / μ := by
  intro x β
  obtain ⟨T, hT, hfirst, hprefix, _⟩ := exists_connection_first_return hμ hu hw
  have hμ1 : 1 ≤ μ := by linarith only [hμ]
  have hu' : 0 ≤ u ∧ u ≤ 1 / 10000 := ⟨hu.1, hu.2.trans (div_le_self (by norm_num) hμ1)⟩
  have hw' : 0 ≤ w ∧ w ≤ 1 := ⟨hw.1.le, hw.2.trans (by norm_num)⟩
  have hD : 0 < projectiveStateDenom (connectionEntry μ u w) :=
    (connection_denom_bound (m := μ) (v := 1) hu' (by norm_num) hw').2
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hβ0 : β 0 = connectionEntry μ u w := by
    dsimp [β]
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  have hA (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 + normalizedMaxCurve x 0 t 0 :=
    lt_of_lt_of_le (by positivity) (hprefix t ht).1
  have H := normalized_connection_endpoint_phase_bound hc hμ (le_refl 0) hT.le hA
    (fun t ht => (hprefix t ht).2)
    (show -β 0 0 = μ by rw [hβ0]; simp [connectionEntry])
    (show β 0 2 = 1 by rw [hβ0]; rfl)
    (show 0 < β 0 3 by simpa [hβ0, connectionEntry] using hw.1) hfirst.1.2.2
  refine ⟨T, hT, hfirst, hprefix, ?_⟩
  change |phaseNorm (-β T 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤
    24 * (β 0 1 + (β 0 3) ^ 2) / μ at H
  simpa [hβ0, connectionEntry] using H

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
open Set

private theorem BianchiIX.connectionReturn_control {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    0 < connectionReturnTime p ∧ ∀ t ∈ Icc 0 (connectionReturnTime p),
      3 / (2 * (p 0) ^ 2) ≤ 1 + normalizedMaxCurve (connectionInitialState p) 0 t 0 ∧
        connectionRegion (p 0) (toProjectiveState (normalizedMaxCurve (connectionInitialState p) 0 t)) := by
  obtain ⟨T, hT, hfirst, hprefix, _⟩ := exists_connection_first_return hμ hu hw
  have heq : connectionReturnTime p = T := hfirst.csInf_eq
  rw [heq]
  exact ⟨hT, hprefix⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionReturn_phase_bound {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    |connectionReturnPhaseError p| ≤ 24 * (p 1 + (p 2) ^ 2) / p 0 := by
  obtain ⟨T, _, hfirst, _, hbound⟩ := exists_connection_phase_bound hμ hu hw
  have heq : connectionReturnTime p = T := hfirst.csInf_eq
  simpa only [connectionReturnPhaseError, connectionReturnState, heq, connectionInitialState] using hbound

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_connectionReturnPhaseError {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    ContDiffAt ℝ 2 connectionReturnPhaseError p := by
  have hstate := (connectionReturn_regular hμ hu hw).2.2.1
  have hcoord : ContDiffAt ℝ 2 (fun q => connectionReturnState q 0) p := contDiffAt_pi.mp hstate 0
  have hleft : ContDiffAt ℝ 2 (fun q => phaseNorm (-connectionReturnState q 0 - 1) 1) p := by
    apply (((hcoord.neg.sub contDiffAt_const).pow 2).add contDiffAt_const).sqrt
    positivity
  have hright : ContDiffAt ℝ 2 (fun q : ConnectionParameters => phaseNorm (q 0 + 1) 1) p := by
    have hq : ContDiffAt ℝ 2 (fun q : ConnectionParameters => q 0 + 1) p := by fun_prop
    apply ((hq.pow 2).add contDiffAt_const).sqrt
    positivity
  exact (hleft.sub hright).add contDiffAt_const

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
open Filter
open scoped Topology

private theorem BianchiIX.connectionReturn_phase_response_bounds_nonneg {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    |fderiv ℝ connectionReturnPhaseError p ![1, 0, 0]| ≤ 50000 * (p 1 + (p 2) ^ 2) / (p 0) ^ 2 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 1, 0]| ≤ 50000 / p 0 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 0, 1]| ≤ 50000 * (p 1 + p 2) / p 0 := by
  by_cases hpos : 0 < p 1
  · exact connectionReturn_phase_response_bounds hμ ⟨hpos, hu.2⟩ hw
  have hp1 : p 1 = 0 := le_antisymm (le_of_not_gt hpos) hu.1
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  let ε : ℝ := (1 / 10000) / p 0
  have hε : 0 < ε := by dsimp [ε]; positivity
  let q : ℕ → ConnectionParameters := fun n => ![p 0, ε / ((n : ℝ) + 1), p 2]
  have hqU (n : ℕ) : 0 < q n 1 ∧ q n 1 ≤ (1 / 10000) / q n 0 := by
    change 0 < ε / ((n : ℝ) + 1) ∧ ε / ((n : ℝ) + 1) ≤ ε
    exact ⟨div_pos hε (by positivity), div_le_self hε.le (by have H : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith only [H])⟩
  have hq : Tendsto q atTop (𝓝 p) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · have H := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
      simpa [q, hp1, div_eq_mul_inv] using H
    · exact tendsto_const_nhds
  have H (n : ℕ) := connectionReturn_phase_response_bounds (p := q n) hμ (hqU n) hw
  have hd (v : ConnectionParameters) : ContinuousAt (fun r => |fderiv ℝ connectionReturnPhaseError r v|) p :=
    (((contDiffAt_connectionReturnPhaseError hμ hu hw).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).abs
  have hRμ : ContinuousAt (fun r : ConnectionParameters => 50000 * (r 1 + (r 2) ^ 2) / (r 0) ^ 2) p := by
    fun_prop (disch := exact pow_ne_zero 2 hμne)
  have hRU : ContinuousAt (fun r : ConnectionParameters => 50000 / r 0) p := by
    exact continuousAt_const.div (continuous_apply (0 : Fin 3)).continuousAt hμne
  have hRW : ContinuousAt (fun r : ConnectionParameters => 50000 * (r 1 + r 2) / r 0) p := by
    fun_prop (disch := exact hμne)
  exact ⟨le_of_tendsto_of_tendsto' ((hd ![1, 0, 0]).tendsto.comp hq) (hRμ.tendsto.comp hq) (fun n => (H n).1),
    le_of_tendsto_of_tendsto' ((hd ![0, 1, 0]).tendsto.comp hq) (hRU.tendsto.comp hq) (fun n => (H n).2.1),
    le_of_tendsto_of_tendsto' ((hd ![0, 0, 1]).tendsto.comp hq) (hRW.tendsto.comp hq) (fun n => (H n).2.2)⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_connectionEntrancePhase (p : ConnectionParameters) :
    HasFDerivAt (fun q : ConnectionParameters => phaseNorm (q 0 + 1) 1)
      (((p 0 + 1) / phaseNorm (p 0 + 1) 1) •
        (ContinuousLinearMap.proj (0 : Fin 3) : ConnectionParameters →L[ℝ] ℝ)) p := by
  have ha := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p).add_const 1
  have H := ((ha.pow 2).add_const 1).sqrt (by positivity : (p 0 + 1) ^ 2 + 1 ≠ 0)
  convert! H using 1
  · ext q
    simp [phaseNorm]
  · ext v
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
    simp only [phaseNorm, one_pow]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connectionReturn_phase_curve_bounds {p : ℝ → ConnectionParameters}
    {v : ConnectionParameters} {x r K M A B U P : ℝ}
    (hp : HasDerivAt p v x) (hr : 0 < r) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hμ : 4 ≤ p x 0) (hi : 1 / p x 0 ≤ K * r)
    (hu : 0 ≤ p x 1 ∧ p x 1 ≤ (1 / 10000) / p x 0)
    (hw : 0 < p x 2 ∧ p x 2 ≤ 1 / 10000)
    (hU : 0 ≤ U) (hP : 0 ≤ P ∧ P ≤ 1) (huU : p x 1 ≤ U) (hwP : p x 2 ≤ P)
    (hv0 : |v 0| ≤ M / r ^ 2) (hv1 : r * |v 1| ≤ A * U) (hv2 : r * |v 2| ≤ B * P) :
    DifferentiableAt ℝ (fun a => connectionReturnPhaseError (p a)) x ∧
      |connectionReturnPhaseError (p x)| ≤ 24 * K * r * (U + P ^ 2) ∧
      |deriv (fun a => connectionReturnPhaseError (p a)) x| ≤
        50000 * (K ^ 2 * M + K * A + K * B) * (U + P ^ 2) := by
  have hw0 := hw.1.le
  have Hreg := (contDiffAt_connectionReturnPhaseError hμ hu hw).differentiableAt (by norm_num)
  have HD := Hreg.hasFDerivAt.comp_hasDerivAt (f := p) x hp
  dsimp only [Function.comp_def] at HD
  have Hcols := connectionReturn_phase_response_bounds_nonneg hμ hu hw
  have Hlinear := three_coordinate_linear_bound (fderiv ℝ connectionReturnPhaseError (p x)) v
  have Hbound := Hlinear.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left Hcols.1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left Hcols.2.1 (abs_nonneg _)))
    (mul_le_mul_of_nonneg_left Hcols.2.2 (abs_nonneg _)))
  refine ⟨HD.differentiableAt, ?_, ?_⟩
  · calc
      _ ≤ 24 * (p x 1 + (p x 2) ^ 2) / p x 0 := connectionReturn_phase_bound hμ hu hw
      _ = 24 * (p x 1 + (p x 2) ^ 2) * (1 / p x 0) := by ring
      _ ≤ 24 * (U + P ^ 2) * (K * r) := by gcongr
      _ = _ := by ring
  · rw [HD.deriv]
    exact Hbound.trans (connection_phase_radial_budget hr hK hM hA hB
      (by linarith only [hμ]) hi hU hP ⟨hu.1, huU⟩ ⟨hw.1.le, hwP⟩ hv0 hv1 hv2)

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
open Set Filter
open scoped Topology

private theorem BianchiIX.coreExitConnectionParameters_differential {Z : CoreAngleState} (hK : 1 < Z 0)
    (v : CoreAngleState) :
    let p := coreExitConnectionParameters Z
    let w := fderiv ℝ coreExitConnectionParameters Z v
    ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * w 0 = v 0 ∧ w 1 = v 1 ∧ w 2 = v 2 := by
  intro p w
  have hc := (contDiffAt_coreExitConnectionParameters 1 hK).differentiableAt (by norm_num)
  have heq : (fun X => phaseNorm (coreExitConnectionParameters X 0 + 1) 1) =ᶠ[𝓝 Z]
      (fun X : CoreAngleState => X 0) := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually (lt_mem_nhds hK)] with X hX
    exact coreExitConnectionParameters_phase hX
  have H := (hasFDerivAt_connectionEntrancePhase p).comp Z hc.hasFDerivAt
  have He := (H.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) Z)
  have Hphase := congrArg (fun A : CoreAngleState →L[ℝ] ℝ => A v) He
  have hcomponent (i : Fin 2) : w i.succ = v i.succ := by
    have Hi : HasFDerivAt (fun X => coreExitConnectionParameters X i.succ)
        (ContinuousLinearMap.proj i.succ : CoreAngleState →L[ℝ] ℝ) Z := by
      fin_cases i <;> exact hasFDerivAt_apply _ _
    have Hd := Hi.fderiv
    rw [fderiv_apply hc i.succ] at Hd
    exact congrArg (fun A : CoreAngleState →L[ℝ] ℝ => A v) Hd
  exact ⟨Hphase, hcomponent 0, hcomponent 1⟩

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
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartConnection_phase_error :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 1 ≤ K ∧ ∃ C : ℝ, 0 < C ∧
        ∀ q P : ℝ, 3 < q → 4 < P → ∃ rstar : ℝ, 0 < rstar ∧
          ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
            ∀ ρ ∈ Icc r (2 * r),
              let s := q / 2 * Real.log (1 / r)
              let Y := restartFastProjectiveEntry h s θ ζ
              let k := restartFastCoreRadius h s θ ζ
              let U := Y ρ 1
              let W := Y ρ 2 * Y ρ 3
              ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
                ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                  (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                    t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                  let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
                  let f := fun a => coreRadius (out a 0) (out a 2)
                  let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
                  let Δ := fun a => connectionReturnPhaseError (p a)
                  let g := fun a => connectionReturnPhysicalState (p a) 0
                  let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + C
                  let R := fun a => 2 / g a - (2 / k a) / (1 - 2 / k a)
                  connectionReturnValid (p ρ) ∧ connectionReturnState (p ρ) = toProjectiveState
                    (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0
                      (s + T + connectionReturnTime (p ρ))) ∧
                  r ≤ 1 ∧ 6 ≤ k ρ ∧ 2 / (K * r) ≤ k ρ ∧ k ρ ≤ K / r ∧
                  0 ≤ U ∧ (0 ≤ W ∧ W ≤ 1) ∧
                  DifferentiableAt ℝ k ρ ∧ DifferentiableAt ℝ f ρ ∧
                  |deriv k ρ| ≤ K / r ^ 2 ∧
                  |f ρ - k ρ| ≤ 16 * K * (U + r * W ^ 2) ∧
                  |deriv (fun a => f a - k a) ρ| ≤
                    4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 ∧
                  DifferentiableAt ℝ Δ ρ ∧ |Δ ρ| ≤ C * r * (U + W ^ 2) ∧
                  |deriv Δ ρ| ≤ C * (U + W ^ 2) ∧
                  DifferentiableAt ℝ g ρ ∧ k ρ / 4 ≤ g ρ ∧
                  DifferentiableAt ℝ R ρ ∧ |R ρ| ≤ 8 * E * K ^ 2 * r ^ 2 * (U + r * W ^ 2) ∧
                  |deriv R ρ| ≤ (8 * E * K ^ 2 + 32 * E * K ^ 4) * (U + r * W) := by
  obtain ⟨hD, hhD, HD⟩ := exists_restartPartialCore_radial_data
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_connection
  refine ⟨min hD hE, lt_min hhD hhE, ?_⟩
  intro h hh L hL
  obtain ⟨K, hK, _, _, HK⟩ := HD h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  let A := (200 * coreVariationBound + 2) * K ^ 2
  let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
  let F := K + 8 * (4096 * coreVariationBound) * K ^ 2
  let CU := K * (1 + 576 * A)
  let CW := K * (1 + B)
  let C := 1 + 24 * K + 50000 * (K ^ 2 * (2 * F) + K * CU + K * CW)
  have hK0 : 0 < K := by linarith only [hK]
  have hA : 0 ≤ A := by dsimp only [A, coreVariationBound]; positivity
  have hB : 0 ≤ B := by dsimp only [B, coreVariationBound]; positivity
  have hF : 0 ≤ F := by dsimp only [F, coreVariationBound]; positivity
  have hCU : 0 ≤ CU := by dsimp only [CU]; positivity
  have hCW : 0 ≤ CW := by dsimp only [CW]; positivity
  have hcoef : 0 ≤ 50000 * (K ^ 2 * (2 * F) + K * CU + K * CW) := by positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨K, hK, C, hC, ?_⟩
  intro q P hq hP
  obtain ⟨rD, hrD, HRD⟩ := HK q P hq hP
  obtain ⟨rE, hrE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min rD rE, lt_min hrD hrE, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hr0 := hr.1
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let k := restartFastCoreRadius h s θ ζ
  let U := Y ρ 1
  let W := Y ρ 2 * Y ρ 3
  obtain ⟨hr1, _, _, _, _, hY, _, hkZ, _, hy, hV, _, hklo, hkhi, hdk, _, hdU, hdW, hdz⟩ :=
    HRD r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ ⟨hζ.1.le, hζ.2⟩ ρ hρ
  have hk : 6 ≤ k ρ := (le_max_left _ _).trans hkZ
  have hk0 : 0 < k ρ := by linarith only [hk]
  have hU : 0 ≤ U := hy.2.2.1.1
  have hW : 0 ≤ W ∧ W ≤ 1 :=
    ⟨hy.2.2.2.1, (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)⟩
  have hU1 : U ≤ 1 := (coreBootstrap_wall_bound hk hy.2.2.1.2).trans (by norm_num)
  have hki : 1 / k ρ ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [(div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo]
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hf, _, _, _, hfval, hfder, _⟩ :=
    exists_partialCore_radial_curve_response ⟨hr.1, hr1⟩ hK hY hk hy hV hklo hkhi hdk hdU hdW hdz
  have hfirstnear := hnear.mono fun _ h => h.1
  obtain ⟨_, _, _, _, _, hu, hw, hu0, hw0, hdu, hdw, _⟩ :=
    partialCore_radial_multiplier_response ⟨hr.1, hr1⟩ hK hY hfirstnear hk hy hV hki hkhi hdk hdU hdW hdz
  obtain ⟨S, _, hfirstS, _, _, hμ, huε, hwε, hdecU, hdecW, hphase, hvalid, _, _, horbit⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩ θ ζ hθ hζ ρ hρ
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hμ huε hwε hdecU hdecW hphase hvalid horbit
  let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
  let f := fun a => coreRadius (out a 0) (out a 2)
  let u := fun a => out a 1
  let w := fun a => out a 3
  let p := fun a => coreExitConnectionParameters ![f a, u a, w a]
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
  rw [← hp] at hμ huε hwε hdecU hdecW hphase hvalid horbit
  have hphase' : phaseNorm (p ρ 0 + 1) 1 = f ρ := by dsimp only [f]; rw [hout]; exact hphase
  have hf1 : 1 < f ρ := by
    have Hb := phaseNorm_ge (b := 1) (show 0 ≤ p ρ 0 + 1 by linarith only [hμ.1])
    rw [hphase'] at Hb
    linarith only [hμ.1, Hb]
  have hkd : DifferentiableAt ℝ k ρ := by
    have H := ((contDiffAt_toCoreAngleState 1 (zero_lt_one.trans hV)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt ρ hY.hasDerivAt
    exact (hasDerivAt_pi.mp H 0).differentiableAt
  change DifferentiableAt ℝ f ρ at hf
  change |deriv (fun a => f a - k a) ρ| ≤
    4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 at hfder
  have hfhi : |deriv f ρ| ≤ F / r ^ 2 := by
    have hs : U + r * W ≤ 2 := by nlinarith only [hU1, mul_le_mul hr1 hW.2 hW.1 (by norm_num : (0 : ℝ) ≤ 1)]
    have He := hfder.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (by dsimp only [coreVariationBound]; positivity)) (sq_nonneg r))
    rw [deriv_fun_sub hf hkd] at He
    calc
      _ = |deriv k ρ + (deriv f ρ - deriv k ρ)| := by congr 1; ring
      _ ≤ |deriv k ρ| + |deriv f ρ - deriv k ρ| := abs_add_le _ _
      _ ≤ K / r ^ 2 + 4 * (4096 * coreVariationBound) * K ^ 2 * 2 / r ^ 2 := add_le_add hdk He
      _ = _ := by dsimp only [F]; ring
  have Hwall := partial_core_connection_wall_budget hr.1 hK0.le hk hki hkhi hA hB hU hu0 hw0 hdecU hdecW hdu hdw
  let v : CoreAngleState := ![deriv f ρ, deriv u ρ, deriv w ρ]
  have hcurve : HasDerivAt (fun a => ![f a, u a, w a]) v ρ := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hf.hasDerivAt
    · exact hu.hasDerivAt
    · exact hw.hasDerivAt
  let ξ := fderiv ℝ coreExitConnectionParameters ![f ρ, u ρ, w ρ] v
  have Hp : HasDerivAt p ξ ρ := ((contDiffAt_coreExitConnectionParameters 1 hf1).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt (f := fun a => ![f a, u a, w a]) ρ hcurve
  have Hξ := coreExitConnectionParameters_differential (Z := ![f ρ, u ρ, w ρ]) hf1 v
  change ((p ρ 0 + 1) / phaseNorm (p ρ 0 + 1) 1) * ξ 0 = deriv f ρ ∧
    ξ 1 = deriv u ρ ∧ ξ 2 = deriv w ρ at Hξ
  have hμi : 1 / p ρ 0 ≤ K * r := by
    apply (div_le_iff₀ (by linarith only [hμ.1] : 0 < p ρ 0)).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    have H' := mul_le_mul_of_nonneg_right hμ.2.1 (mul_pos hK0 hr.1).le
    nlinarith only [H, H']
  have hξ0 : |ξ 0| ≤ 2 * |deriv f ρ| := by
    let R := (p ρ 0 + 1) / phaseNorm (p ρ 0 + 1) 1
    have HR := (phaseNorm_ratio_bounds (b := 1) (by linarith only [hμ.1] : 2 ≤ p ρ 0 + 1) (by norm_num)).1
    have HR0 : 0 ≤ R := by dsimp only [R]; linarith only [HR]
    have HE : R * |ξ 0| = |deriv f ρ| := by rw [← Hξ.1, abs_mul, abs_of_nonneg HR0]
    nlinarith only [mul_le_mul_of_nonneg_right HR (abs_nonneg (ξ 0)), HE, abs_nonneg (ξ 0)]
  have HΔ := connectionReturn_phase_curve_bounds Hp hr.1 hK0.le (by positivity : 0 ≤ 2 * F) hCU hCW
    hμ.1 hμi ⟨huε.1.le, huε.2⟩ hwε hU hW Hwall.1 hdecW
    (hξ0.trans ((mul_le_mul_of_nonneg_left hfhi (by norm_num)).trans_eq (by ring)))
    (by rw [Hξ.2.1]; exact Hwall.2.1) (by rw [Hξ.2.2]; exact Hwall.2.2)
  have hΔval : |connectionReturnPhaseError (p ρ)| ≤ C * r * (U + W ^ 2) :=
    HΔ.2.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show 24 * K ≤ C by dsimp only [C]; linarith only [hcoef]) hr.1.le)
      (by positivity))
  have hΔder : |deriv (fun a => connectionReturnPhaseError (p a)) ρ| ≤ C * (U + W ^ 2) :=
    HΔ.2.2.trans (mul_le_mul_of_nonneg_right
      (show 50000 * (K ^ 2 * (2 * F) + K * CU + K * CW) ≤ C by dsimp only [C]; linarith only [hK0])
      (by positivity))
  let Δ := fun a => connectionReturnPhaseError (p a)
  let g := fun a => connectionReturnPhysicalState (p a) 0
  let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + C
  have hE : 0 ≤ E := by dsimp only [E, coreVariationBound]; positivity
  have Hgerm : g =ᶠ[𝓝 ρ] (fun a => f a - 2 + Δ a) := by
    filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hf1)] with a ha
    have Hphase := coreExitConnectionParameters_phase (Z := ![f a, u a, w a]) ha
    change phaseNorm (p a 0 + 1) 1 = f a at Hphase
    dsimp only [g, Δ, connectionReturnPhysicalState, connectionReturnPhaseError]
    simp only [Matrix.cons_val_zero, Hphase]
    ring
  have Hg : HasDerivAt g (deriv f ρ + deriv Δ ρ) ρ :=
    ((hf.hasDerivAt.sub_const 2).add HΔ.1.hasDerivAt).congr_of_eventuallyEq Hgerm
  have hglo : k ρ / 4 ≤ g ρ := by
    have Hcontrol := connectionReturn_control hμ.1 ⟨huε.1.le, huε.2⟩ hwε
    have Hregion := (Hcontrol.2 (connectionReturnTime (p ρ)) ⟨Hcontrol.1.le, le_rfl⟩).2
    change connectionRegion (p ρ 0) (connectionReturnState (p ρ)) at Hregion
    have HM := (abs_le.mp Hregion.1).1
    have Hleft : p ρ 0 / 2 ≤ -connectionReturnState (p ρ) 0 - 1 := by linarith only [HM, hμ.1]
    have Hnorm := phaseNorm_ge (b := 1) (show 0 ≤ -connectionReturnState (p ρ) 0 - 1 by linarith only [Hleft, hμ.1])
    change _ ≤ g ρ at Hnorm
    linarith only [hμ.2.1, Hleft, Hnorm]
  have hW0 := hW.1
  have hRU : r * U ≤ U := mul_le_of_le_one_left hU hr1
  have hvalue : |g ρ - (k ρ - 2)| ≤ E * (U + r * W ^ 2) := by
    have heq : g ρ - (k ρ - 2) = (f ρ - k ρ) + Δ ρ := by rw [Hgerm.self_of_nhds]; ring
    rw [heq]
    have HΔvalue : |Δ ρ| ≤ C * (U + r * W ^ 2) := hΔval.trans (by
      have H := mul_le_mul_of_nonneg_left hRU hC.le
      nlinarith only [H])
    have Htotal := (abs_add_le (f ρ - k ρ) (Δ ρ)).trans (add_le_add hfval HΔvalue)
    have Hextra : 0 ≤ (4 * (4096 * coreVariationBound) * K ^ 2) * (U + r * W ^ 2) := by
      dsimp only [coreVariationBound]
      positivity
    dsimp only [E]
    nlinarith only [Htotal, Hextra]
  have hder : |deriv g ρ - deriv k ρ| ≤ E * (U + r * W) / r ^ 2 := by
    have hRW : 0 ≤ r * W ∧ r * W ≤ 1 :=
      ⟨mul_nonneg hr.1.le hW.1, (mul_le_mul hr1 hW.2 hW.1 (by norm_num)).trans_eq (by ring)⟩
    have hsmall : r ^ 2 * (U + W ^ 2) ≤ U + r * W := by
      have hr2 : r ^ 2 ≤ 1 := by nlinarith only [hr.1, hr1]
      nlinarith only [mul_le_mul_of_nonneg_right hr2 hU,
        mul_le_mul_of_nonneg_right hRW.2 hRW.1]
    have Hδ : |deriv Δ ρ| ≤ C * (U + r * W) / r ^ 2 := hΔder.trans (by
      apply (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr
      have H := mul_le_mul_of_nonneg_left hsmall hC.le
      nlinarith only [H])
    have Hf := hfder
    rw [deriv_fun_sub hf hkd] at Hf
    rw [Hg.deriv]
    have Htotal := (abs_add_le (deriv f ρ - deriv k ρ) (deriv Δ ρ)).trans (add_le_add Hf Hδ)
    have Hextra : 0 ≤ 16 * K * (U + r * W) / r ^ 2 := by positivity
    calc
      _ = |(deriv f ρ - deriv k ρ) + deriv Δ ρ| := by congr 1; ring
      _ ≤ 4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 + C * (U + r * W) / r ^ 2 := Htotal
      _ ≤ 16 * K * (U + r * W) / r ^ 2 +
          (4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 + C * (U + r * W) / r ^ 2) := le_add_of_nonneg_left Hextra
      _ = _ := by dsimp only [E]; ring
  have Hrec := connection_reciprocal_radial_bounds ⟨hr.1, hr1⟩ hK hE hU hW
    Hg.differentiableAt hkd hk hklo hglo hdk hvalue hder
  exact ⟨T, hT, hfirst, τ, hτ, hcτ, hfirstnear, hvalid, horbit, hr1, hk, hklo, hkhi,
    hU, hW, hkd, hf, hdk, hfval, hfder, HΔ.1, hΔval, hΔder, Hg.differentiableAt, hglo, Hrec⟩

end
end

/-- The full E.14 phase approximation and its positive ordinary radial slope at the actual restart. -/
theorem solution :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let F := fun a => restartReferenceRadialPhase h (restartRadialCurve θ ζ a)
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                  t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
                let f := fun a => coreRadius (out a 0) (out a 2)
                let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
                let xr := fun a => 2 / connectionReturnPhysicalState (p a) 0
                connectionReturnValid (p ρ) ∧ connectionReturnState (p ρ) = toProjectiveState
                  (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0
                    (s + T + connectionReturnTime (p ρ))) ∧
                DifferentiableAt ℝ xr ρ ∧ |xr ρ - F ρ| ≤ C * r ^ 2 ∧
                |deriv xr ρ - deriv F ρ| ≤ C * r ∧
                1 / (8 * Real.sqrt 3) ≤ deriv xr ρ ∧ deriv xr ρ ≤ C := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartConnection_phase_error
  obtain ⟨hF, hhF, HF⟩ := exists_restartFastProjectionPhase_approximation
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  refine ⟨min hE (min hF hV), lt_min hhE (lt_min hhF hhV), ?_⟩
  intro h hh L hL
  obtain ⟨K, hK, Cδ, hCδ, HKE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨KF, hKF, HKF⟩ := HF h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL
  let M := 8 * (L + 1)
  let B := 32 * h + 2048 * M
  let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + Cδ
  let D := (2 * L + 3) / Real.sqrt 3 + 1
  let V := 8 * E * K ^ 2 * B
  let A := (8 * E * K ^ 2 + 32 * E * K ^ 4) * B
  let H := A + 8 * K * D
  let C := 1 + KF + (V + 2 * K ^ 2) + H + D
  have hK0 : 0 < K := by linarith only [hK]
  have hM : 0 < M := by dsimp only [M]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity [hh.1]
  have hE : 0 < E := by dsimp only [E, coreVariationBound]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hH : 0 < H := by dsimp only [H]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rE, hrE, HRE⟩ := HKE q P hq hP
  obtain ⟨rF, hrF, HRF⟩ := HKF q hq2
  obtain ⟨rV, hrV, HRV⟩ := HV h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩ L hL q hq2
  refine ⟨min rE (min rF (min rV (min 1 (1 / (8 * Real.sqrt 3 * H))))),
    lt_min hrE (lt_min hrF (lt_min hrV (lt_min (by norm_num) (by positivity)))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hr0 := hr.1
  have hrF' := hr.2.trans (min_le_right _ _)
  have hrV' := hrF'.trans (min_le_right _ _)
  have hrB' := hrV'.trans (min_le_right _ _)
  have hr1 := hrB'.trans (min_le_left _ _)
  have hrH := hrB'.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1.le, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1 (by linarith only [hP] : (2 : ℝ) ≤ P)
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let k := restartFastCoreRadius h s θ ζ
  let x := restartFastProjectionPhase h s θ ζ
  let F := fun a => restartReferenceRadialPhase h (restartRadialCurve θ ζ a)
  let U := Y ρ 1
  let W := Y ρ 2 * Y ρ 3
  obtain ⟨_, _, hx, hxval, hxder, hxlo, hxhi⟩ :=
    HRF r ⟨hr.1, hrF'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hu, _, hw, _⟩ :=
    HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hvalid, horbit, _, hk6, hklo, _, hU, hW,
    _, _, _, _, _, _, _, _, _, _, hRD, hRv, hRd⟩ := HRE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
  let f := fun a => coreRadius (out a 0) (out a 2)
  let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
  let xr := fun a => 2 / connectionReturnPhysicalState (p a) 0
  let R := fun a => xr a - x a / (1 - x a)
  let Q := fun a => x a / (1 - x a) - x a
  change DifferentiableAt ℝ R ρ at hRD
  change |R ρ| ≤ 8 * E * K ^ 2 * r ^ 2 * (U + r * W ^ 2) at hRv
  change |deriv R ρ| ≤ (8 * E * K ^ 2 + 32 * E * K ^ 4) * (U + r * W) at hRd
  have Hsum := (restart_entry_linear_amplitude_budget ⟨hr.1, hr1⟩ hh.1.le hM.le hq hP
    ⟨hζ.1.le, hζ.2⟩ ⟨hu.1.le, hu.2⟩ hw).2.2
  change U + W ≤ B * r at Hsum
  have hW0 := hW.1
  have hWsq : r * W ^ 2 ≤ W := by
    have HW := mul_le_mul_of_nonneg_right hW.2 hW.1
    nlinarith only [HW, mul_le_mul_of_nonneg_right hr1 (sq_nonneg W)]
  have hvalueBudget : U + r * W ^ 2 ≤ B :=
    (add_le_add le_rfl hWsq).trans (Hsum.trans (mul_le_of_le_one_right hB.le hr1))
  have hderBudget : U + r * W ≤ B * r :=
    (add_le_add le_rfl (mul_le_of_le_one_left hW.1 hr1)).trans Hsum
  have HRv : |R ρ| ≤ V * r ^ 2 := hRv.trans
    ((mul_le_mul_of_nonneg_left hvalueBudget (by positivity)).trans_eq (by dsimp only [V]; ring))
  have HRd : |deriv R ρ| ≤ A * r := hRd.trans
    ((mul_le_mul_of_nonneg_left hderBudget (by positivity)).trans_eq (by dsimp only [A]; ring))
  have hk0 : 0 < k ρ := by linarith only [hk6]
  have hx0 : 0 ≤ x ρ := (div_pos (by norm_num) hk0).le
  have hxhalf : x ρ ≤ 1 / 2 := by
    change 2 / k ρ ≤ 1 / 2
    apply (div_le_iff₀ hk0).mpr
    linarith only [hk6]
  have hxr : x ρ ≤ K * r := by
    change 2 / k ρ ≤ K * r
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [(div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo]
  have hdx0 : 0 ≤ deriv x ρ := (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.sqrt 3)).trans hxlo
  have hdx : |deriv x ρ| ≤ D := by rw [abs_of_nonneg hdx0]; exact hxhi
  obtain ⟨hQD, HQv, HQd⟩ := mobius_radial_correction_bounds hx hr.1.le hK0.le hD.le ⟨hx0, hxhalf⟩ hxr hdx
  change DifferentiableAt ℝ Q ρ at hQD
  have HX : HasDerivAt xr (deriv R ρ + deriv Q ρ + deriv x ρ) ρ := by
    apply ((hRD.hasDerivAt.add hQD.hasDerivAt).add hx.hasDerivAt).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun a => by
      change xr a = (R a + Q a) + x a
      dsimp only [R, Q]
      ring
  have Hder : |deriv xr ρ - deriv x ρ| ≤ H * r := by
    rw [HX.deriv]
    have Htri := (abs_add_le (deriv R ρ) (deriv Q ρ)).trans (add_le_add HRd HQd)
    simpa only [add_sub_cancel_right, show A * r + 8 * K * D * r = H * r by dsimp only [H]; ring] using Htri
  have Hsmall : H * r ≤ 1 / (8 * Real.sqrt 3) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt 3)).mpr
    nlinarith only [(le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt 3 * H)).mp hrH]
  have Hquarter : 1 / (8 * Real.sqrt 3) ≤ 1 := by
    have Hs : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
    exact (div_le_one (by positivity)).mpr (by linarith only [Hs])
  refine ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hvalid, horbit, HX.differentiableAt, ?_, ?_, ?_, ?_⟩
  · have heq : xr ρ - F ρ = R ρ + Q ρ + (x ρ - F ρ) := by dsimp only [R, Q]; ring
    rw [heq]
    have Htri := (abs_add_le (R ρ + Q ρ) (x ρ - F ρ)).trans
      (add_le_add ((abs_add_le (R ρ) (Q ρ)).trans (add_le_add HRv HQv)) hxval)
    have HC : V + 2 * K ^ 2 + KF ≤ C := by dsimp only [C]; linarith only [hH, hD]
    exact Htri.trans (by nlinarith only [mul_le_mul_of_nonneg_right HC (sq_nonneg r)])
  · have Htri := (abs_sub_le (deriv xr ρ) (deriv x ρ) (deriv F ρ)).trans (add_le_add Hder hxder)
    have HC : H + KF ≤ C := by dsimp only [C]; nlinarith only [hV, sq_nonneg K, hD]
    exact Htri.trans (by nlinarith only [mul_le_mul_of_nonneg_right HC hr.1.le])
  · have Heq : 1 / (4 * Real.sqrt 3) = 2 * (1 / (8 * Real.sqrt 3)) := by ring
    rw [Heq] at hxlo
    linarith only [(abs_le.mp Hder).1, hxlo, Hsmall]
  · have HC : D + 1 ≤ C := by dsimp only [C]; nlinarith only [hKF, hV, sq_nonneg K, hH]
    linarith only [(abs_le.mp Hder).2, hxhi, Hsmall, Hquarter, HC]
