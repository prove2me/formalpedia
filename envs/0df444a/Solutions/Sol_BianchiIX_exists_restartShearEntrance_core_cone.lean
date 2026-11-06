-- Prove2me | solution 1 for BianchiIX.exists_restartShearEntrance_core_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:52:43.622592+00:00
-- url     : https://prove2.me/submissions/2c428c9c-3f83-4c38-ad7c-48730cd3e9f0

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Definitions.Def_BianchiIX_Dynamics_CoreExitFactor
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_Dynamics_CoreMultiplierDifferential
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_ShearTransportData
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_coreRadiusReturn_large_regular
import Theorems.Thm_BianchiIX_entranceReturn_active_component
import Theorems.Thm_BianchiIX_entranceReturn_decay
import Theorems.Thm_BianchiIX_entranceReturn_region
import Theorems.Thm_BianchiIX_entranceReturn_regular
import Theorems.Thm_BianchiIX_entrance_denom_bounds
import Theorems.Thm_BianchiIX_entrance_phase_bounds
import Theorems.Thm_BianchiIX_exists_entrance_physical_curve_bounds
import Theorems.Thm_BianchiIX_exists_entrance_wall_sqrt_curve_bounds
import Theorems.Thm_BianchiIX_exists_large_core_exit_derivative
import Theorems.Thm_BianchiIX_exists_large_core_invariant_cone
import Theorems.Thm_BianchiIX_exists_partialCore_downward_radius_response
import Theorems.Thm_BianchiIX_exists_restartFastShearCore_response
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_homogeneous_cone_of_unit
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.scaled_quotient_radial_derivative_bound {f g : ℝ → ℝ} {f' g' t r c Kf Kg : ℝ}
    (Hf : HasDerivAt f f' t) (Hg : HasDerivAt g g' t)
    (hr : 0 < r) (hc : 0 ≤ c) (hf : 0 ≤ f t) (hg : 0 < g t)
    (hf' : |f'| ≤ Kf * f t / r) (hg' : |g'| ≤ Kg * g t / r) :
    DifferentiableAt ℝ (fun x => c * f x / g x) t ∧
      |deriv (fun x => c * f x / g x) t| ≤ (Kf + Kg) * (c * f t / g t) / r := by
  have HD := (Hf.const_mul c).div Hg (ne_of_gt hg)
  change HasDerivAt (fun x => c * f x / g x) _ t at HD
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv, abs_div, abs_of_nonneg (sq_nonneg (g t))]
  calc
    _ ≤ ((c * |f'|) * g t + (c * f t) * |g'|) / (g t) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have H := abs_sub_le (c * f' * g t) 0 (c * f t * g')
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_nonneg hc,
        abs_of_nonneg hf, abs_of_pos hg] using H
    _ ≤ ((c * (Kf * f t / r)) * g t + (c * f t) * (Kg * g t / r)) / (g t) ^ 2 := by
      gcongr
    _ = _ := by field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.product_radial_derivative_bound {f g : ℝ → ℝ} {t r Kf Kg : ℝ}
    (Hf : DifferentiableAt ℝ f t) (Hg : DifferentiableAt ℝ g t)
    (hf : 0 ≤ f t) (hg : 0 ≤ g t)
    (hf' : |deriv f t| ≤ Kf * f t / r) (hg' : |deriv g t| ≤ Kg * g t / r) :
    DifferentiableAt ℝ (fun x => f x * g x) t ∧
      |deriv (fun x => f x * g x) t| ≤ (Kf + Kg) * (f t * g t) / r := by
  have HD := Hf.hasDerivAt.mul Hg.hasDerivAt
  change HasDerivAt (fun x => f x * g x) _ t at HD
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv]
  calc
    _ ≤ |deriv f t * g t| + |f t * deriv g t| := abs_add_le _ _
    _ = |deriv f t| * g t + f t * |deriv g t| := by rw [abs_mul, abs_mul, abs_of_nonneg hf, abs_of_nonneg hg]
    _ ≤ (Kf * f t / r) * g t + f t * (Kg * g t / r) := by gcongr
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.log_radial_derivative_bound {f : ℝ → ℝ} {t r K : ℝ}
    (Hf : DifferentiableAt ℝ f t) (hf : 0 < f t)
    (hf' : |deriv f t| ≤ K * f t / r) :
    DifferentiableAt ℝ (fun x => Real.log (f x)) t ∧
      |deriv (fun x => Real.log (f x)) t| ≤ K / r := by
  have HD := Hf.hasDerivAt.log (ne_of_gt hf)
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv, abs_div, abs_of_pos hf]
  calc
    _ ≤ (K * f t / r) / f t := div_le_div_of_nonneg_right hf' hf.le
    _ = _ := by field_simp

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

private theorem BianchiIX.homogeneous_phase_ratio_of_unit
    (D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) {R a b A : ℝ}
    (hunit : ∀ z : Fin 3 → ℝ, R * z 0 = 1 → |z 1| ≤ a → |z 2| ≤ b →
      |D z 0 - 1| ≤ A)
    (v : Fin 3 → ℝ) (hc : R * v 0 ≠ 0)
    (hva : |v 1| ≤ a * |R * v 0|) (hvb : |v 2| ≤ b * |R * v 0|) :
    |D v 0 / (R * v 0) - 1| ≤ A := by
  let c := R * v 0
  have hc' : c ≠ 0 := hc
  let z := c⁻¹ • v
  have hz0 : R * z 0 = 1 := by
    change R * (c⁻¹ * v 0) = 1
    calc
      _ = c⁻¹ * c := by dsimp only [c]; ring
      _ = 1 := inv_mul_cancel₀ hc
  have hz (i : Fin 3) (s : ℝ) (hi : |v i| ≤ s * |c|) : |z i| ≤ s := by
    change |c⁻¹ * v i| ≤ s
    rw [abs_mul, abs_inv]
    calc
      _ ≤ |c|⁻¹ * (s * |c|) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (abs_nonneg _))
      _ = s := by field_simp
  have H := hunit z hz0 (hz 1 a hva) (hz 2 b hvb)
  have hd : D z 0 = D v 0 / c := by
    dsimp only [z]
    rw [map_smul]
    change c⁻¹ * D v 0 = D v 0 / c
    ring
  rwa [hd] at H

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

private theorem BianchiIX.coreAngle_section_sign (m : ℝ) :
    (coreAngle m 1 < 0 ↔ 1 < m) ∧ (0 < coreAngle m 1 ↔ m < 1) := by
  simp only [coreAngle, div_one, Real.arsinh_neg_iff, Real.arsinh_pos_iff]
  constructor <;> constructor <;> intro h <;> linarith

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
open Set

private theorem BianchiIX.coreAngle_entry_eq_neg_arcosh {m : ℝ} (hm : 1 < m) :
    coreAngle m 1 = -Real.arcosh (coreRadius m 1) := by
  have H := Real.arcosh_cosh (neg_nonneg.mpr ((coreAngle_section_sign m).1.mpr hm).le)
  rw [Real.cosh_neg, cosh_coreAngle (by norm_num : (0 : ℝ) < 1), div_one] at H
  linarith

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

private theorem BianchiIX.entranceRegion_phase {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    4 / 5 * k ≤ y 0 - 1 ∧ y 0 - 1 ≤ 101 / 100 * k :=
  entrance_phase_bounds hk hy.1 hy.2.1 hy.2.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadius_coreRadiusEntry {Y : CoreAngleState} (hk : 1 < Y 0) :
    coreRadius (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 := by
  have hk0 : 0 < Y 0 := lt_trans zero_lt_one hk
  have hsq := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ Y 0 ^ 2 - 1)
  have he : coreEnergy (coreRadiusEntry Y 0) (coreRadiusEntry Y 2) = Y 0 ^ 2 := by
    dsimp [coreRadiusEntry, coreEnergy]
    nlinarith only [hsq]
  rw [coreRadius, he, Real.sqrt_sq hk0.le]

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
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusEntry_region {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    coreRegion (Y 0) (coreRadiusEntry Y) := by
  have hR := coreRadius_coreRadiusEntry (by linarith only [hk] : 1 < Y 0)
  have he := coreRadius_sq (coreRadiusEntry Y 0) (coreRadiusEntry Y 2)
  rw [hR] at he
  refine ⟨?_, le_rfl, hu, ?_⟩
  · rw [← he, sub_self, abs_zero]
    norm_num
  · simpa [coreRadiusEntry] using hw

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
open Set

private theorem BianchiIX.entranceReturn_walls_nonincreasing {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    entranceReturnState y 1 ≤ y 1 ∧ entranceReturnState y 3 ≤ y 3 := by
  have H := entranceReturn_decay hk hm hu hv hw
  have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith only [hk]
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hEs : Real.exp (-coreRadius (y 0) (y 2) * -Real.log (y 2) / 3) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk0.le) hL) (by norm_num))
  have hEw : Real.exp (-(-Real.log (y 2)) / coreRadius (y 0) (y 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)
  constructor
  · exact H.1.trans ((mul_le_mul_of_nonneg_left hEs (mul_nonneg hu.1 hv.1.le)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hv.2.le hu.1]))
  · exact H.2.trans ((mul_le_mul_of_nonneg_left hEw (mul_nonneg hw.1 hv.1.le)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hv.2.le hw.1]))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.entranceReturn_partialCore_entry {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    let k := coreRadius (y 0) (y 2)
    let z := entranceReturnState y
    let κ := coreRadius (z 0) (z 2)
    6 ≤ κ ∧ (99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k) ∧
      z 2 = 1 ∧ 1 < z 0 ∧ coreRegion κ z ∧
      (0 ≤ z 1 ∧ z 1 ≤ y 1) ∧ (0 ≤ z 3 ∧ z 3 ≤ y 2 * y 3) ∧
      z 1 + z 2 * z 3 ≤ η / κ ∧ projectiveCoreAngle z = -Real.arcosh κ := by
  intro k z κ
  have hk' : 7 / 4 ≤ k := by linarith only [hk]
  have hk0 : 0 < k := by linarith only [hk]
  have HE := (entranceReturn_regular hk' hm hu hv hw).1
  have HR := entranceReturn_region hk' hm hu hv hw _ ⟨HE.1.1.1.le, le_rfl⟩
  change entranceRegion k z at HR
  have hκ : 99 / 100 * k ≤ κ ∧ κ ≤ 101 / 100 * k := by
    have H := abs_le.mp HR.2.1
    change - (k / 100) ≤ κ - k ∧ κ - k ≤ k / 100 at H
    constructor <;> linarith only [H.1, H.2]
  have hκ6 : 6 ≤ κ := by linarith only [hk, hκ.1]
  have hκ0 : 0 < κ := by linarith only [hκ6]
  have hhit : z 2 = 1 := (entranceReturn_active_component hk' hm hu hv hw).1
  have hm' : 1 < z 0 := by
    have H := (entranceRegion_phase hk' HR).1
    linarith only [H, hk]
  have hU := (entranceReturn_walls_nonincreasing hk' hm hu hv hw).1
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hExp : Real.exp (-(-Real.log (y 2)) / k) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hk0.le)
  have hW : z 3 ≤ y 2 * y 3 := (entranceReturn_decay hk' hm hu hv hw).2.trans
    ((mul_le_of_le_one_right (mul_nonneg hw.1 hv.1.le) hExp).trans_eq (mul_comm _ _))
  have hsum : z 1 + z 2 * z 3 ≤ η / κ := by
    rw [hhit, one_mul]
    exact (add_le_add hU hW).trans (hsmall.trans
      (div_le_div_of_nonneg_left hη.1.le hκ0 (by linarith only [hκ.2, hk0])))
  have hprod : 0 ≤ z 2 * z 3 := mul_nonneg HR.2.2.2.1.1 HR.2.2.2.2.1
  refine ⟨hκ6, hκ, hhit, hm', partialCoreEntry_region hκ6 (by rw [hhit])
    HR.2.2.1.1 hprod hη.2 hsum, ⟨HR.2.2.1.1, hU⟩, ⟨HR.2.2.2.2.1, hW⟩, hsum, ?_⟩
  change coreAngle (z 0) (z 2) = -Real.arcosh (coreRadius (z 0) (z 2))
  rw [hhit]
  exact coreAngle_entry_eq_neg_arcosh hm'

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
open Set Filter
open scoped Topology

private theorem BianchiIX.entranceReturn_downward_restart {y : ProjectiveState} {T : ℝ}
    (hD : 0 < projectiveStateDenom y) (HE : entranceReturnValid y)
    (HT : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState (entranceReturnState y)) 0 ∧
      projectiveOriginalFlow (entranceReturnState y) 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState (entranceReturnState y)) 0 t < 0} T) :
    IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0}
        (entranceReturnTime y + T) ∧
    partialCoreDownwardReturnTime y = entranceReturnTime y + T ∧
    partialCoreDownwardReturnState y = toCoreAngleState (projectiveOriginalFlow (entranceReturnState y) 0 T) := by
  let S := entranceReturnTime y
  let z := entranceReturnState y
  have hS : 0 < S := HE.1.1.1
  have hT : 0 < T := HT.1.1
  have hA := (HE.2.1 S ⟨hS.le, le_rfl⟩).2
  have hc := fromProjectiveState_constraint hD.ne'
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hS.le
  have hbase : fromProjectiveState z = normalizedMaxCurve (fromProjectiveState y) 0 S :=
    fromProjectiveState_toProjectiveState hA.ne' ((normalizedMaxCurve_constraint hdom).trans hc)
  have hcz : stateConstraint (fromProjectiveState z) = 1 := by
    rw [hbase]
    exact (normalizedMaxCurve_constraint hdom).trans hc
  have Hflow (t : ℝ) (ht : 0 ≤ t) :
      normalizedMaxCurve (fromProjectiveState z) 0 t = normalizedMaxCurve (fromProjectiveState y) 0 (S + t) := by
    rw [hbase]
    have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hdom)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hS.le))
    simpa only [zero_add, add_comm t S] using H
  have Hproj (t : ℝ) (ht : 0 ≤ t) : projectiveOriginalFlow z 0 t = projectiveOriginalFlow y 0 (S + t) :=
    congrArg toProjectiveState (Hflow t ht)
  have Hrate (t : ℝ) (ht : 0 ≤ t) :
      normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t =
        normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 (S + t) := by
    unfold normalizedEventRate
    rw [Hflow t ht]
  have Hleast : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0}
        (S + T) := by
    refine ⟨⟨add_pos hS hT, normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_pos hS hT).le, ?_, ?_⟩, ?_⟩
    · rw [← Hproj T hT.le]
      exact HT.1.2.2.1
    · rw [← Hrate T hT.le]
      exact HT.1.2.2.2
    · intro t ht
      by_cases htS : t ≤ S
      · have H := HE.2.2.2 t ⟨ht.1.le, htS⟩
        linarith only [H, ht.2.2.2]
      · have hsub : 0 < t - S := sub_pos.mpr (lt_of_not_ge htS)
        have HP := Hproj (t - S) hsub.le
        have HR := Hrate (t - S) hsub.le
        rw [add_sub_cancel] at HP HR
        have H := HT.2 ⟨hsub, normalizedMaxDomain_contains_Ici_of_constraint hcz 0 hsub.le,
          by rw [HP]; exact ht.2.2.1, by rw [HR]; exact ht.2.2.2⟩
        linarith only [H]
  have Htime := partialCoreDownwardReturnTime_eq Hleast
  refine ⟨Hleast, Htime, ?_⟩
  unfold partialCoreDownwardReturnState
  rw [Htime, ← Hproj T hT.le]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entrancePartialCore_downward_regular {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    let z := entranceReturnState y
    IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧ normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0}
        (partialCoreDownwardReturnTime y) ∧
      partialCoreDownwardReturnTime y = entranceReturnTime y + partialCoreDownwardReturnTime z ∧
      partialCoreDownwardReturnState y = partialCoreDownwardReturnState z ∧
      ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
      (partialCoreDownwardReturnTime =ᶠ[𝓝 y] fun w => entranceReturnTime w + partialCoreDownwardReturnTime (entranceReturnState w)) ∧
      (partialCoreDownwardReturnState =ᶠ[𝓝 y] fun w => partialCoreDownwardReturnState (entranceReturnState w)) := by
  intro z
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm hu hv hw
  obtain ⟨hκ, _, hhit, hmz, hregion, _⟩ := entranceReturn_partialCore_entry hk hm hu hv hw hη hsmall
  have HC := partialCoreDownwardReturn_regular hκ hregion rfl (Or.inr ⟨hhit, hmz.le⟩)
  have hD := entrance_initial_denom_pos hk' hm hu hv hw
  have hDc : Continuous projectiveStateDenom := by unfold projectiveStateDenom projectiveDenom curvature; fun_prop
  have Hnear := HE.2.2.1.continuousAt.tendsto.eventually HC.2.2.2.1
  have Hboth : ∀ᶠ w in 𝓝 y,
      partialCoreDownwardReturnTime w = entranceReturnTime w + partialCoreDownwardReturnTime (entranceReturnState w) ∧
      partialCoreDownwardReturnState w = partialCoreDownwardReturnState (entranceReturnState w) := by
    filter_upwards [hDc.continuousAt.eventually (lt_mem_nhds hD), HE.2.2.2.2.2, Hnear] with w hd he hc
    exact (entranceReturn_downward_restart hd he hc.1).2
  have Htime := Hboth.mono fun _ h => h.1
  have Hstate := Hboth.mono fun _ h => h.2
  have Hbase := entranceReturn_downward_restart hD HE.1 HC.2.2.2.1.self_of_nhds.1
  have ht : ContDiffAt ℝ 2 partialCoreDownwardReturnTime y :=
    (HE.2.1.add (ContDiffAt.comp (g := partialCoreDownwardReturnTime) y HC.2.1 HE.2.2.1)).congr_of_eventuallyEq Htime
  have hz : ContDiffAt ℝ 2 partialCoreDownwardReturnState y :=
    (ContDiffAt.comp (g := partialCoreDownwardReturnState) y HC.2.2.1 HE.2.2.1).congr_of_eventuallyEq Hstate
  refine ⟨?_, Htime.self_of_nhds, Hstate.self_of_nhds, ht, hz, Htime, Hstate⟩
  rw [Htime.self_of_nhds]
  exact Hbase.1

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

private theorem BianchiIX.coreRadiusEntry_of_upward_section {y : ProjectiveState}
    (hm : 1 ≤ y 0) (hv : y 2 = 1) :
    coreRadiusEntry (toCoreAngleState y) = y := by
  have he : coreEnergy (y 0) (y 2) = (y 0 - 1) ^ 2 + 1 := by
    simp only [coreEnergy, hv, one_pow]
  have hs : coreRadius (y 0) (y 2) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    rw [coreRadius, Real.sq_sqrt (by rw [he]; positivity), he]
    ring
  ext i
  fin_cases i
  · change 1 + Real.sqrt (coreRadius (y 0) (y 2) ^ 2 - 1) = y 0
    rw [hs, Real.sqrt_sq (sub_nonneg.mpr hm)]
    ring
  · rfl
  · exact hv.symm
  · change y 2 * y 3 = y 3
    rw [hv, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusReturn_downward_eventuallyEq {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    (coreRadiusReturnTime =ᶠ[𝓝 Y] fun Z => partialCoreDownwardReturnTime (coreRadiusEntry Z)) ∧
      (coreReturnState coreRadiusReturnTime =ᶠ[𝓝 Y]
        fun Z => partialCoreDownwardReturnState (coreRadiusEntry Z)) := by
  have hk1 : 1 < Y 0 := by linarith only [hk]
  have he := contDiffAt_coreRadiusEntry 2 hk1
  have hr := coreRadiusReturn_large_regular hk hu hw
  have hd := partialCoreDownwardReturn_regular hk (coreRadiusEntry_region hk hu hw)
    (coreRadius_coreRadiusEntry hk1) (Or.inr ⟨rfl, by
      change (1 : ℝ) ≤ 1 + Real.sqrt (Y 0 ^ 2 - 1)
      linarith only [Real.sqrt_nonneg (Y 0 ^ 2 - 1)]⟩)
  obtain ⟨T, _, hfirst, _, _, _, σ, _, _, _, huniq, _⟩ :=
    exists_large_core_exit_derivative hk hu hw
  have ht : coreRadiusReturnTime Y = T := hr.2.2.2.self_of_nhds.unique hfirst
  have hdt : partialCoreDownwardReturnTime (coreRadiusEntry Y) = T := hd.1.unique hfirst
  have hpair : ContinuousAt (fun Z => (coreRadiusEntry Z, coreRadiusReturnTime Z)) Y :=
    he.continuousAt.prodMk hr.2.1.continuousAt
  have hpaird : ContinuousAt (fun Z =>
      (coreRadiusEntry Z, partialCoreDownwardReturnTime (coreRadiusEntry Z))) Y :=
    he.continuousAt.prodMk (hd.2.1.continuousAt.comp he.continuousAt)
  have hn : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0 (coreRadiusReturnTime Z) 2 = 1 ↔
        σ (coreRadiusEntry Z) = coreRadiusReturnTime Z := by
    have hlocal : ∀ᶠ z : ProjectiveState × ℝ in
        𝓝 (coreRadiusEntry Y, coreRadiusReturnTime Y),
        projectiveOriginalFlow z.1 0 z.2 2 = 1 ↔ σ z.1 = z.2 := by
      simpa only [ht, coreRadiusEntry] using huniq
    exact hpair.eventually hlocal
  have hnd : ∀ᶠ Z in 𝓝 Y,
      projectiveOriginalFlow (coreRadiusEntry Z) 0
        (partialCoreDownwardReturnTime (coreRadiusEntry Z)) 2 = 1 ↔
        σ (coreRadiusEntry Z) = partialCoreDownwardReturnTime (coreRadiusEntry Z) := by
    have hlocal : ∀ᶠ z : ProjectiveState × ℝ in
        𝓝 (coreRadiusEntry Y, partialCoreDownwardReturnTime (coreRadiusEntry Y)),
        projectiveOriginalFlow z.1 0 z.2 2 = 1 ↔ σ z.1 = z.2 := by
      rw [hdt]
      simpa only [coreRadiusEntry] using huniq
    exact hpaird.eventually hlocal
  have hdown := he.continuousAt.tendsto.eventually hd.2.2.2.1
  have htime : coreRadiusReturnTime =ᶠ[𝓝 Y]
      fun Z => partialCoreDownwardReturnTime (coreRadiusEntry Z) := by
    filter_upwards [hn, hnd, hr.2.2.2, hdown] with Z hZ hZd hfull hdown
    exact (hZ.mp hfull.1.2).symm.trans (hZd.mp hdown.1.1.2.2.1)
  refine ⟨htime, ?_⟩
  filter_upwards [htime] with Z hZ
  simp only [coreReturnState, partialCoreDownwardReturnState, hZ]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRadiusReturn_large_contDiff_two {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ContDiffAt ℝ 2 coreRadiusReturnTime Y ∧
      ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y := by
  have hk1 : 1 < Y 0 := by linarith only [hk]
  have he := contDiffAt_coreRadiusEntry 2 hk1
  have hd := partialCoreDownwardReturn_regular hk (coreRadiusEntry_region hk hu hw)
    (coreRadius_coreRadiusEntry hk1) (Or.inr ⟨rfl, by
      change (1 : ℝ) ≤ 1 + Real.sqrt (Y 0 ^ 2 - 1)
      linarith only [Real.sqrt_nonneg (Y 0 ^ 2 - 1)]⟩)
  have hg := coreRadiusReturn_downward_eventuallyEq hk hu hw
  exact ⟨(hd.2.1.comp Y he).congr_of_eventuallyEq hg.1,
    (hd.2.2.1.comp Y he).congr_of_eventuallyEq hg.2⟩

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
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_coreRadiusReturn_large_cone_margin :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ Y : CoreAngleState, 6 ≤ Y 0 →
      (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
      ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let F := coreReturnState coreRadiusReturnTime
        let d := fderiv ℝ F Y v
        0 < d 0 ∧ |d 0 - 1| ≤ 1 / (32 * Y 0) ∧
          ∀ i : Fin 2, |d i.succ| ≤
            (1 - 1 / (16 * Y 0)) * Real.sqrt (F Y i.succ) * d 0 := by
  obtain ⟨ε, hε, hεsmall, Hε⟩ := exists_large_core_invariant_cone
  refine ⟨ε, hε, hεsmall, ?_⟩
  intro Y hk hu hw
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hsmall := div_le_div_of_nonneg_right hεsmall hk0.le
  have hu' := And.intro hu.1 (hu.2.trans hsmall)
  have hw' := And.intro hw.1 (hw.2.trans hsmall)
  obtain ⟨τ, _, _, _, hnear, Hcone⟩ := Hε Y hk hu hw
  have hcanonical := (coreRadiusReturn_large_regular hk hu' hw').2.2.2
  have htime : coreRadiusReturnTime =ᶠ[𝓝 Y] τ := by
    filter_upwards [hcanonical, hnear] with Z hc ht
    exact hc.unique ht.1
  have hstate : coreReturnState coreRadiusReturnTime =ᶠ[𝓝 Y] coreReturnState τ := by
    filter_upwards [htime] with Z hZ
    simp only [coreReturnState, hZ]
  refine ⟨(coreRadiusReturn_large_contDiff_two hk hu' hw').2, ?_⟩
  intro v hv0 hv1 hv2 F d
  obtain ⟨hpos, hrad, hc1, hc2⟩ := Hcone v hv0 hv1 hv2
  have hderiv : d = fderiv ℝ (coreReturnState τ) Y v := by
    dsimp only [d, F]
    rw [hstate.fderiv_eq]
  rw [hderiv]
  refine ⟨hpos, hrad, ?_⟩
  intro i
  change |fderiv ℝ (coreReturnState τ) Y v i.succ| ≤
    (1 - 1 / (16 * Y 0)) * Real.sqrt (coreReturnState coreRadiusReturnTime Y i.succ) *
      fderiv ℝ (coreReturnState τ) Y v 0
  rw [hstate.self_of_nhds]
  fin_cases i
  · exact hc1
  · exact hc2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_coreRadiusReturn_curve_cone :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ (Y : ℝ → CoreAngleState) (x : ℝ),
      DifferentiableAt ℝ Y x → 6 ≤ Y x 0 →
      (0 ≤ Y x 1 ∧ Y x 1 ≤ ε / Y x 0) → (0 ≤ Y x 2 ∧ Y x 2 ≤ ε / Y x 0) →
      deriv (fun t => Y t 0) x < 0 →
      (∀ i : Fin 2, |deriv (fun t => Y t i.succ) x| ≤
        Real.sqrt (Y x i.succ) * |deriv (fun t => Y t 0) x|) →
      let G := fun t => coreReturnState coreRadiusReturnTime (Y t)
      DifferentiableAt ℝ G x ∧ deriv (fun t => G t 0) x < 0 ∧
        |deriv (fun t => G t 0) x / deriv (fun t => Y t 0) x - 1| ≤ 1 / (32 * Y x 0) ∧
        (3 / 4 ≤ deriv (fun t => G t 0) x / deriv (fun t => Y t 0) x ∧
          deriv (fun t => G t 0) x / deriv (fun t => Y t 0) x ≤ 5 / 4) ∧
        ∀ i : Fin 2, |deriv (fun t => G t i.succ) x| ≤
          (1 - 1 / (16 * Y x 0)) * Real.sqrt (G x i.succ) * |deriv (fun t => G t 0) x| := by
  obtain ⟨ε, hε, hεsmall, Hε⟩ := exists_coreRadiusReturn_large_cone_margin
  refine ⟨ε, hε, hεsmall, ?_⟩
  intro Y x hY hk hu hw hneg hwall G
  obtain ⟨hF, Hunit⟩ := Hε (Y x) hk hu hw
  let D := fderiv ℝ (coreReturnState coreRadiusReturnTime) (Y x)
  let v := deriv Y x
  have hv (i : Fin 3) : deriv (fun t => Y t i) x = v i :=
    (hasDerivAt_pi.mp hY.hasDerivAt i).deriv
  have HD : HasDerivAt G (D v) x :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hd (i : Fin 3) : deriv (fun t => G t i) x = D v i :=
    (hasDerivAt_pi.mp HD i).deriv
  have hvneg : v 0 < 0 := by rwa [hv 0] at hneg
  have hva : |v 1| ≤ Real.sqrt (Y x 1) * |(1 : ℝ) * v 0| := by
    simpa [hv] using hwall 0
  have hvb : |v 2| ≤ Real.sqrt (Y x 2) * |(1 : ℝ) * v 0| := by
    simpa [hv] using hwall 1
  have HR := homogeneous_phase_ratio_of_unit D (R := 1)
    (fun z hz hzu hzw => (Hunit z (by simpa only [one_mul] using hz) hzu hzw).2.1)
    v (by simpa only [one_mul] using hvneg.ne) hva hvb
  have HC := homogeneous_cone_of_unit D (R := 1) (by norm_num)
    (A := (1 - 1 / (16 * Y x 0)) * Real.sqrt (G x 1))
    (B := (1 - 1 / (16 * Y x 0)) * Real.sqrt (G x 2))
    (fun z hz hzu hzw => by
      have H := Hunit z (by simpa only [one_mul] using hz) hzu hzw
      exact ⟨H.1.le, H.2.2 0, H.2.2 1⟩) v hva hvb
  simp only [one_mul] at HR
  have hsmall : 1 / (32 * Y x 0) ≤ (1 / 4 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith only [hk]
  have Hbounds : 3 / 4 ≤ D v 0 / v 0 ∧ D v 0 / v 0 ≤ 5 / 4 := by
    have H := abs_le.mp (HR.trans hsmall)
    constructor <;> linarith only [H.1, H.2]
  have Hneg : D v 0 < 0 := by
    have Hpos : 0 < D v 0 / v 0 := lt_of_lt_of_le (by norm_num) Hbounds.1
    exact ((div_pos_iff.mp Hpos).resolve_left (fun h => (not_lt_of_ge hvneg.le) h.2)).1
  refine ⟨HD.differentiableAt, ?_, ?_, ?_, ?_⟩
  · rwa [hd]
  · simpa only [hd, hv] using HR
  · simpa only [hd, hv] using Hbounds
  · intro i
    simp only [hd]
    fin_cases i
    · exact HC.1
    · exact HC.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entrancePartialCore_fullCore_eventuallyEq {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    (partialCoreDownwardReturnTime =ᶠ[𝓝 y] fun w => entranceReturnTime w +
      coreRadiusReturnTime (toCoreAngleState (entranceReturnState w))) ∧
      (partialCoreDownwardReturnState =ᶠ[𝓝 y] fun w =>
        coreReturnState coreRadiusReturnTime (toCoreAngleState (entranceReturnState w))) := by
  let z := entranceReturnState y
  let X := toCoreAngleState z
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm hu hv hw
  obtain ⟨hκ, _, hhit, hmz, _, hU, hW, hsum, _⟩ :=
    entranceReturn_partialCore_entry hk hm hu hv hw hη hsmall
  change 6 ≤ X 0 at hκ
  change z 2 = 1 at hhit
  change 1 < z 0 at hmz
  have hXU : 0 ≤ X 1 := hU.1
  have hXW : 0 ≤ X 2 := by change 0 ≤ z 2 * z 3; rw [hhit, one_mul]; exact hW.1
  have hκ0 : 0 ≤ X 0 := by linarith only [hκ]
  change X 1 + X 2 ≤ η / X 0 at hsum
  have hsum' : X 1 + X 2 ≤ (1 / 10000) / X 0 := hsum.trans
    (div_le_div_of_nonneg_right hη.2 hκ0)
  have HG := coreRadiusReturn_downward_eventuallyEq hκ
    ⟨hXU, (le_add_of_nonneg_right hXW).trans hsum'⟩
    ⟨hXW, (le_add_of_nonneg_left hXU).trans hsum'⟩
  have hcoord : ContinuousAt (fun w => toCoreAngleState (entranceReturnState w)) y :=
    (contDiffAt_toCoreAngleState 2 (by change 0 < z 2; rw [hhit]; norm_num)).continuousAt.comp HE.2.2.1.continuousAt
  have hrecover : ∀ᶠ w in 𝓝 y,
      coreRadiusEntry (toCoreAngleState (entranceReturnState w)) = entranceReturnState w := by
    have hM : ContinuousAt (fun w => entranceReturnState w 0) y :=
      (continuous_apply 0).continuousAt.comp HE.2.2.1.continuousAt
    filter_upwards [HE.2.2.2.2.2, hM.eventually (lt_mem_nhds hmz)] with w he hm'
    apply coreRadiusEntry_of_upward_section hm'.le
    exact he.1.1.2.2
  have HD := entrancePartialCore_downward_regular hk hm hu hv hw hη hsmall
  constructor
  · filter_upwards [HD.2.2.2.2.2.1, hcoord.eventually HG.1, hrecover] with w hd hg hr
    rw [hr] at hg
    exact hd.trans (congrArg (entranceReturnTime w + ·) hg.symm)
  · filter_upwards [HD.2.2.2.2.2.2, hcoord.eventually HG.2, hrecover] with w hd hg hr
    rw [hr] at hg
    exact hd.trans hg.symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.entranceReturn_coreCoordinates_eventuallyEq {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    (fun w => toCoreAngleState (entranceReturnState w)) =ᶠ[𝓝 y] fun w =>
      ![coreRadius (entranceReturnState w 0) (entranceReturnState w 2),
        entranceReturnState w 1, entranceReturnState w 3] := by
  filter_upwards [(entranceReturn_regular hk hm hu hv hw).2.2.2.2.2] with w hw'
  have hv' : entranceReturnState w 2 = 1 := hw'.1.1.2.2
  simp only [toCoreAngleState, hv', one_mul]

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
open Set

private theorem BianchiIX.exists_restartFastShearProjectiveEntry_response :
    ∃ hstar > (0 : ℝ), ∃ K > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε σ n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := q / 2 * Real.log (1 / a)
          let Y := restartFastShearProjectiveEntry h T σ n₂ n₃
          let p := fun t => Y t 2 * Y t 3
          T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
          DifferentiableAt ℝ Y ρ ∧ |deriv (fun t => Y t 0) ρ| ≤ K / a ^ 2 ∧
          (∀ i : Fin 3, 0 ≤ Y ρ i.succ ∧
            |deriv (fun t => Y t i.succ) ρ| ≤ K * Y ρ i.succ / a ∧
            (0 < Y ρ i.succ → DifferentiableAt ℝ (fun t => Real.log (Y t i.succ)) ρ ∧
              |deriv (fun t => Real.log (Y t i.succ)) ρ| ≤ K / a)) ∧
          DifferentiableAt ℝ p ρ ∧ 0 ≤ p ρ ∧ |deriv p ρ| ≤ K * p ρ / a ∧
          (0 < n₂ → 0 < n₃ → 0 < p ρ ∧
            |deriv (fun t => Real.log (Y t 1)) ρ| + |deriv (fun t => Real.log (Y t 2)) ρ| +
              |deriv (fun t => Real.log (Y t 3)) ρ| ≤ K / a) ∧
          (n₂ = 0 → Y ρ 2 = 0 ∧ deriv (fun t => Y t 2) ρ = 0) ∧
          (n₃ = 0 → Y ρ 3 = 0 ∧ deriv (fun t => Y t 3) ρ = 0) ∧
          (n₂ = 0 ∨ n₃ = 0 → p ρ = 0 ∧ deriv p ρ = 0) := by
  obtain ⟨C, hC, hE, hhE, HE⟩ := exists_restartShearFastEntry_control
  obtain ⟨hP, hhP, HP⟩ := exists_restartFastShearProjectiveEntry_bounds
  let B := 8 * C + 2048
  let K := 4 * B + 40000
  have hB : 0 < B := by dsimp only [B]; linarith only [hC]
  have hK : 0 < K := by dsimp only [K]; positivity
  have hBK : B ≤ K := by dsimp only [K]; linarith only [hB]
  have h2BK : B + B ≤ K := by dsimp only [K]; linarith only [hB]
  have h3BK : 3 * B ≤ K := by dsimp only [K]; linarith only [hB]
  have hMK : (4 + 2048) * 18 ≤ K := by dsimp only [K]; linarith only [hB]
  refine ⟨min hE hP, lt_min hhE hhP, K, hK, ?_⟩
  intro h hh q hq
  obtain ⟨aE, haE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  obtain ⟨aP, haP, HRP⟩ := HP h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q hq
  refine ⟨min aE aP, lt_min haE haP, ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T Y p
  let Z := restartShearCurve σ n₂ n₃ ρ
  let P := fun t => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t)
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
  let A := restartFastShearHeight h T σ n₂ n₃
  obtain ⟨_, _, _, _, _, _, _, Hcurve, hnpos, _, hs, _, hv, hnrel, hw⟩ :=
    HRE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  obtain ⟨hdom, HYD, HAD, HAlo, _, HAd, HMval, HUval, HVval, HWval, _, _⟩ :=
    HRP a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  change HasDerivAt P v ρ at Hcurve
  change ‖v‖ ≤ 2 at hv
  change 0 < (P ρ).1 at hnpos
  change |v.1| ≤ 2 * (P ρ).1 / a at hnrel
  change 3 * a / 4 ≤ σ * (P ρ).2 0 ∧ σ * (P ρ).2 0 ≤ 9 * a / 4 at hs
  change DifferentiableAt ℝ A ρ at HAD
  change a ^ 2 / 4 ≤ A ρ at HAlo
  change |deriv A ρ| ≤ 512 * a at HAd
  change DifferentiableAt ℝ Y ρ at HYD
  change 1 / (8 * a) ≤ σ * Y ρ 0 ∧ σ * Y ρ 0 ≤ 18 / a at HMval
  have hA : 0 < A ρ := (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le HAlo
  have HArel : |deriv A ρ| ≤ 2048 * A ρ / a := by
    apply (le_div_iff₀ ha.1).mpr
    nlinarith only [mul_le_mul_of_nonneg_right HAd ha.1.le, HAlo]
  have Hn : HasDerivAt (fun t => (P t).1) v.1 ρ :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ Hcurve
  have Hc (i : Fin 3) : HasDerivAt (fun t => (P t).2 i) (v.2 i) ρ := by
    let Q : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact Q.hasFDerivAt.comp_hasDerivAt ρ
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ Hcurve)
  have Hvc (i : Fin 3) : |v.2 i| ≤ 2 := (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have Hnrel : |v.1| ≤ (8 * C) * (P ρ).1 / a := hnrel.trans (by
    apply div_le_div_of_nonneg_right _ ha.1.le
    exact mul_le_mul_of_nonneg_right (by linarith only [hC]) hnpos.le)
  have Hweak (i : Fin 2) : 0 ≤ (P ρ).2 i.succ ∧ |v.2 i.succ| ≤ (8 * C) * (P ρ).2 i.succ / a := by
    have hZi : 0 ≤ Z i.succ := by fin_cases i; exact h₂.1; exact h₃.1
    exact ⟨(div_nonneg hZi (by norm_num)).trans (hw i).1, (hw i).2.2⟩
  have HU := scaled_quotient_radial_derivative_bound Hn HAD.hasDerivAt ha.1
    (Real.sqrt_nonneg (3 : ℝ)) hnpos.le hA Hnrel HArel
  have HV := scaled_quotient_radial_derivative_bound (Hc 1) HAD.hasDerivAt ha.1
    (Real.sqrt_nonneg (3 : ℝ)) (Hweak 0).1 hA (Hweak 0).2 HArel
  have HW := scaled_quotient_radial_derivative_bound (Hc 2) HAD.hasDerivAt ha.1
    (Real.sqrt_nonneg (3 : ℝ)) (Hweak 1).1 hA (Hweak 1).2 HArel
  change DifferentiableAt ℝ (fun t => Y t 1) ρ ∧ |deriv (fun t => Y t 1) ρ| ≤ B * Y ρ 1 / a at HU
  change DifferentiableAt ℝ (fun t => Y t 2) ρ ∧ |deriv (fun t => Y t 2) ρ| ≤ B * Y ρ 2 / a at HV
  change DifferentiableAt ℝ (fun t => Y t 3) ρ ∧ |deriv (fun t => Y t 3) ρ| ≤ B * Y ρ 3 / a at HW
  have hu : 0 < Y ρ 1 := HUval.1
  have hvpos : 0 ≤ Y ρ 2 := (div_nonneg h₂.1 (by positivity)).trans HVval.1
  have hwpos : 0 ≤ Y ρ 3 := (div_nonneg h₃.1 (by positivity)).trans HWval.1
  have HMder : |deriv (fun t => Y t 0) ρ| ≤ K / a ^ 2 := by
    have hspos : 0 ≤ σ * (P ρ).2 0 := (by positivity [ha.1] : 0 ≤ 3 * a / 4).trans hs.1
    have Hsrel : |σ * v.2 0| ≤ 4 * (σ * (P ρ).2 0) / a := by
      rw [abs_mul, hσ, one_mul]
      apply (Hvc 0).trans
      apply (le_div_iff₀ ha.1).mpr
      linarith only [hs.1, ha.1]
    have HM := scaled_quotient_radial_derivative_bound ((Hc 0).const_mul σ) HAD.hasDerivAt ha.1
      (Real.sqrt_nonneg (3 : ℝ)) hspos hA Hsrel HArel
    have heq : (fun t => Real.sqrt 3 * (σ * (P t).2 0) / A t) = fun t => σ * Y t 0 := by
      funext t
      change Real.sqrt 3 * (σ * (P t).2 0) / A t = σ * (Real.sqrt 3 * (P t).2 0 / A t)
      ring
    rw [heq] at HM
    rw [((differentiableAt_pi.mp HYD 0).hasDerivAt.const_mul σ).deriv, abs_mul, hσ, one_mul] at HM
    rw [congr_fun heq ρ] at HM
    calc
      _ ≤ (4 + 2048) * (σ * Y ρ 0) / a := HM.2
      _ ≤ (4 + 2048) * (18 / a) / a := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left HMval.2 (by norm_num)) ha.1.le
      _ = ((4 + 2048) * 18) / a ^ 2 := by ring
      _ ≤ K / a ^ 2 := div_le_div_of_nonneg_right hMK (sq_nonneg a)
  have Hwalls (i : Fin 3) : 0 ≤ Y ρ i.succ ∧
      |deriv (fun t => Y t i.succ) ρ| ≤ B * Y ρ i.succ / a := by
    fin_cases i
    · exact ⟨hu.le, HU.2⟩
    · exact ⟨hvpos, HV.2⟩
    · exact ⟨hwpos, HW.2⟩
  have Hprod := product_radial_derivative_bound HV.1 HW.1 hvpos hwpos HV.2 HW.2
  change DifferentiableAt ℝ p ρ ∧ |deriv p ρ| ≤ (B + B) * p ρ / a at Hprod
  have hprod : 0 ≤ p ρ := mul_nonneg hvpos hwpos
  have Hzero (i : Fin 3) (hz : Y ρ i.succ = 0) : deriv (fun t => Y t i.succ) ρ = 0 :=
    abs_nonpos_iff.mp (by simpa only [hz, mul_zero, zero_div] using (Hwalls i).2)
  have Hvzero (hz : n₂ = 0) : Y ρ 2 = 0 := by
    have H : Y ρ 2 ≤ 16 * n₂ / a ^ 2 := HVval.2
    rw [hz, mul_zero, zero_div] at H
    exact le_antisymm H hvpos
  have Hwzero (hz : n₃ = 0) : Y ρ 3 = 0 := by
    have H : Y ρ 3 ≤ 16 * n₃ / a ^ 2 := HWval.2
    rw [hz, mul_zero, zero_div] at H
    exact le_antisymm H hwpos
  refine ⟨hdom, HYD, HMder, ?_, Hprod.1, hprod,
    Hprod.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2BK hprod) ha.1.le),
    ?_, fun hz => ⟨Hvzero hz, Hzero 1 (Hvzero hz)⟩,
    fun hz => ⟨Hwzero hz, Hzero 2 (Hwzero hz)⟩, ?_⟩
  · intro i
    refine ⟨(Hwalls i).1, (Hwalls i).2.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBK (Hwalls i).1) ha.1.le), ?_⟩
    intro hpos
    have Hlog := log_radial_derivative_bound (differentiableAt_pi.mp HYD i.succ) hpos (Hwalls i).2
    exact ⟨Hlog.1, Hlog.2.trans (div_le_div_of_nonneg_right hBK ha.1.le)⟩
  · intro h₂pos h₃pos
    have hV : 0 < Y ρ 2 := (by positivity [ha.1] : 0 < n₂ / (12 * a ^ 2)).trans_le HVval.1
    have hW : 0 < Y ρ 3 := (by positivity [ha.1] : 0 < n₃ / (12 * a ^ 2)).trans_le HWval.1
    refine ⟨mul_pos hV hW, ?_⟩
    have HUlog := log_radial_derivative_bound HU.1 hu HU.2
    have HVlog := log_radial_derivative_bound HV.1 hV HV.2
    have HWlog := log_radial_derivative_bound HW.1 hW HW.2
    exact (add_le_add (add_le_add HUlog.2 HVlog.2) HWlog.2).trans (by
      have H := div_le_div_of_nonneg_right h3BK ha.1.le
      convert! H using 1
      ring)
  · intro hz
    have hpzero : p ρ = 0 := by
      rcases hz with hz | hz
      · change Y ρ 2 * Y ρ 3 = 0
        rw [Hvzero hz, zero_mul]
      · change Y ρ 2 * Y ρ 3 = 0
        rw [Hwzero hz, mul_zero]
    exact ⟨hpzero, abs_nonpos_iff.mp (by simpa only [hpzero, mul_zero, zero_div] using Hprod.2)⟩

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
open Set

private theorem BianchiIX.exists_restartShearEntrance_inputs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
              let k := restartFastShearCoreRadius h s 1 n₂ n₃ ρ
              y 2 < 1 →
              0 ≤ s ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
              s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
              0 < restartFastShearHeight h s 1 n₂ n₃ ρ ∧
              8 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧ 1 < y 0 ∧
              (0 < y 1 ∧ y 1 ≤ 1 / 10000) ∧ (0 < y 2 ∧ y 2 < 1) ∧
              (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) ∧ y 1 + y 2 * y 3 ≤ η / (2 * k) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_entry
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hE hV, lt_min hhE hhV, ?_⟩
  intro h hh q P hq hP η hη
  have hηhalf : η / 2 ∈ Ioc (0 : ℝ) (1 / 10000) := ⟨by positivity [hη.1], by linarith only [hη.2]⟩
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP (η / 2) hηhalf
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q (by linarith only [hq])
  refine ⟨min aE (min aV (1 / 512)), lt_min haE (lt_min haV (by norm_num)), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s y k hv
  have haV' := ha.2.trans (min_le_right _ _)
  have ha512 : a ≤ 1 / 512 := haV'.trans (min_le_right _ _)
  have ha1 : a ≤ 1 := ha512.trans (by norm_num)
  obtain ⟨hs, hrad, hdom, hA, hm, _, hklo, hkhi, _, hu0, hp0, hsum, _⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, hV, hW, _⟩ :=
    HaV a ⟨ha.1, haV'.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num) ⟨h₂.1.le, h₂.2⟩ h₃ ρ hρ
  have hk8 : 8 ≤ k := (show 8 ≤ 1 / (16 * a) by
    apply (le_div_iff₀ (by positivity [ha.1])).mpr
    linarith only [ha512]).trans hklo
  have hsmall : y 1 + y 2 * y 3 ≤ η / (2 * k) := hsum.trans_eq (by ring)
  have hu : y 1 ≤ 1 / 10000 := ((le_add_of_nonneg_right hp0).trans hsmall).trans
    ((div_le_self hη.1.le (by linarith only [hk8])).trans hη.2)
  have hv0 : 0 < y 2 := (div_pos h₂.1 (by positivity [ha.1])).trans_le hV.1
  have hw0 : 0 ≤ y 3 := (div_nonneg h₃.1 (by positivity)).trans hW.1
  have hn₃ : n₃ ≤ a ^ (4 : ℕ) := h₃P.trans (by
    have H := Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hP.le
    rw [show a ^ (4 : ℝ) = a ^ (4 : ℕ) from Real.rpow_natCast a 4] at H
    exact H)
  have hw : y 3 ≤ 1 / 10000 := by
    calc
      _ ≤ 16 * n₃ / a ^ 2 := hW.2
      _ ≤ 16 * a ^ 4 / a ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn₃ (by norm_num)) (sq_nonneg a)
      _ = 16 * a ^ 2 := by field_simp
      _ ≤ _ := by
        have H := pow_le_pow_left₀ ha.1.le ha512 2
        norm_num at H
        linarith only [H]
  exact ⟨hs, hrad, hdom, hA, hk8, hklo, hkhi, hm, ⟨hu0, hu⟩, ⟨hv0, hv⟩, ⟨hw0, hw⟩, hsmall⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearEntrance_differential_inputs :
    ∃ hstar > (0 : ℝ), ∃ D > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ δ ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
              let k := coreRadius (Y ρ 0) (Y ρ 2)
              Y ρ 2 < 1 → DifferentiableAt ℝ Y ρ ∧
              8 ≤ k ∧ 1 / (16 * a) ≤ k ∧ k ≤ 32 / a ∧ 1 < Y ρ 0 ∧
              (0 < Y ρ 1 ∧ Y ρ 1 ≤ δ) ∧ (0 < Y ρ 2 ∧ Y ρ 2 < 1) ∧ (0 < Y ρ 3 ∧ Y ρ 3 ≤ δ) ∧
              Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ δ / (2 * k) ∧
              |deriv (fun t => Y t 0) ρ| ≤ D * k ^ 2 ∧
              ∀ i : Fin 4, i ≠ 0 → |deriv (fun t => Y t i) ρ| ≤ D * k * Y ρ i := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearEntrance_inputs
  obtain ⟨hR, hhR, K, hK, HR⟩ := exists_restartFastShearProjectiveEntry_response
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  let D := 256 * K
  refine ⟨min hE (min hR hV), lt_min hhE (lt_min hhR hhV), D, by dsimp only [D]; positivity, ?_⟩
  intro h hh q P hq hP δ hδ
  have hh' := hh.2.trans (min_le_right _ _)
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP δ hδ
  obtain ⟨aR, haR, HaR⟩ := HR h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q (by linarith only [hq])
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh'.trans (min_le_right _ _)⟩ q (by linarith only [hq])
  refine ⟨min aE (min aR (min aV (min 1 (δ / 16)))),
    lt_min haE (lt_min haR (lt_min haV (lt_min zero_lt_one (by positivity [hδ.1])))), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k hv
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  have hasmall := ha''.trans (min_le_right _ _)
  have ha1 : a ≤ 1 := hasmall.trans (min_le_left _ _)
  have haδ : a ≤ δ / 16 := hasmall.trans (min_le_right _ _)
  obtain ⟨_, _, _, _, hk8, hklo, hkhi, hm, hu, hv', hw, hsum⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  obtain ⟨_, HY, HM, Hwall, _⟩ := HaR a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε
    (by norm_num) ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, HW, _⟩ := HaV a ⟨ha.1, ha''.trans (min_le_left _ _)⟩
    ε 1 n₂ n₃ hε (by norm_num) ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ ρ hρ
  change 8 ≤ k at hk8
  change 1 / (16 * a) ≤ k at hklo
  change k ≤ 32 / a at hkhi
  change 0 < Y ρ 2 ∧ Y ρ 2 < 1 at hv'
  change 0 ≤ Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000 at hw
  change Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ δ / (2 * k) at hsum
  have hkpos : 0 < k := by linarith only [hk8]
  have hUδ : Y ρ 1 ≤ δ := ((le_add_of_nonneg_right (mul_nonneg hv'.1.le hw.1)).trans hsum).trans
    (div_le_self hδ.1.le (by linarith only [hk8]))
  have hWpos : 0 < Y ρ 3 := (div_pos h₃.1 (by positivity [ha.1])).trans_le HW.1
  have hn₃ : n₃ ≤ a ^ (4 : ℕ) := h₃P.trans (by
    have H := Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hP.le
    rw [show a ^ (4 : ℝ) = a ^ (4 : ℕ) from Real.rpow_natCast a 4] at H
    exact H)
  have hWδ : Y ρ 3 ≤ δ := by
    calc
      _ ≤ 16 * n₃ / a ^ 2 := HW.2
      _ ≤ 16 * a ^ 4 / a ^ 2 := by gcongr
      _ = 16 * a ^ 2 := by field_simp
      _ ≤ 16 * a := by nlinarith only [mul_le_mul_of_nonneg_left ha1 ha.1.le]
      _ ≤ δ := by linarith only [(le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mp haδ]
  have hki : 1 / a ≤ 16 * k := by
    calc
      _ = 16 * (1 / (16 * a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hklo (by norm_num)
  have Hd0 : |deriv (fun t => Y t 0) ρ| ≤ D * k ^ 2 := HM.trans (by
    calc
      _ = K * (1 / a) ^ 2 := by ring
      _ ≤ K * (16 * k) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity [ha.1]) hki 2) hK.le
      _ = _ := by dsimp only [D]; ring)
  have HDwall (i : Fin 3) : |deriv (fun t => Y t i.succ) ρ| ≤ D * k * Y ρ i.succ := by
    calc
      _ ≤ K * Y ρ i.succ / a := (Hwall i).2.1
      _ = (K * Y ρ i.succ) * (1 / a) := by ring
      _ ≤ (K * Y ρ i.succ) * (16 * k) :=
        mul_le_mul_of_nonneg_left hki (mul_nonneg hK.le (Hwall i).1)
      _ ≤ _ := by dsimp only [D]; nlinarith only [mul_nonneg (mul_nonneg hK.le hkpos.le) (Hwall i).1]
  refine ⟨HY, hk8, hklo, hkhi, hm, ⟨hu.1, hUδ⟩, hv', ⟨hWpos, hWδ⟩, hsum, Hd0, ?_⟩
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · exact HDwall 0
  · exact HDwall 1
  · exact HDwall 2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearEntrance_radial_response :
    ∃ hstar > (0 : ℝ), ∃ B > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let k := restartFastShearCoreRadius h s 1 n₂ n₃
            let κ := fun t => coreRadius (entranceReturnState (Y t) 0) (entranceReturnState (Y t) 2)
            Y ρ 2 < 1 →
            DifferentiableAt ℝ κ ρ ∧ 6 ≤ κ ρ ∧ 1 / (32 * a) ≤ κ ρ ∧ κ ρ ≤ 64 / a ∧
            |κ ρ - k ρ| ≤ B * a ∧ |deriv κ ρ - deriv k ρ| ≤ B / a ∧
            1 / (8192 * a ^ 2) ≤ -deriv κ ρ ∧ -deriv κ ρ ≤ 1537 / a ^ 2 := by
  obtain ⟨C, hC, δ, hδ, hδsmall, HC⟩ := exists_entrance_physical_curve_bounds
  obtain ⟨hI, hhI, D, hD, HI⟩ := exists_restartShearEntrance_differential_inputs
  obtain ⟨hG, hhG, _, _, HG⟩ := exists_restartFastShearCore_response
  let B := 48 * C + 96 * C * D + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBC : 48 * C ≤ B := by dsimp only [B]; linarith only [mul_pos hC hD]
  have hBCD : 96 * C * D ≤ B := by dsimp only [B]; linarith only [hC]
  refine ⟨min hI hG, lt_min hhI hhG, B, hB, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aI, haI, HaI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aG, haG, HaG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P
    (by linarith only [hq]) (by linarith only [hP])
  refine ⟨min aI (min aG (1 / (8192 * B))), lt_min haI (lt_min haG (by positivity)), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k κ hv
  have ha' := ha.2.trans (min_le_right _ _)
  have haB : a ≤ 1 / (8192 * B) := ha'.trans (min_le_right _ _)
  obtain ⟨HY, hk8, hklo, hkhi, hm, huδ, hv', hwδ, hsum, Hd0, HDwall'⟩ :=
    HaI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, _, _, Hklo, Hkhi, _⟩ := HaG a ⟨ha.1, ha'.trans (min_le_left _ _)⟩
    ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  change 8 ≤ k ρ at hk8
  change 1 / (16 * a) ≤ k ρ at hklo
  change k ρ ≤ 32 / a at hkhi
  change Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ δ / (2 * k ρ) at hsum
  change 1 / (4096 * a ^ 2) ≤ -deriv k ρ at Hklo
  change -deriv k ρ ≤ 1536 / a ^ 2 at Hkhi
  have hkpos : 0 < k ρ := by linarith only [hk8]
  have hu : 0 < Y ρ 1 ∧ Y ρ 1 ≤ 1 / 10000 := ⟨huδ.1, huδ.2.trans hδsmall⟩
  have hw : 0 ≤ Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000 := ⟨hwδ.1.le, hwδ.2.trans hδsmall⟩
  have hk' : 7 / 4 ≤ coreRadius (Y ρ 0) (Y ρ 2) := by change 7 / 4 ≤ k ρ; linarith only [hk8]
  obtain ⟨Hκ, _, Hval, Hder⟩ := HC Y ρ D HY hD.le hk' hm.le huδ hv' hwδ Hd0 HDwall'
  let b := Y ρ 1 + Y ρ 3
  let H := Y ρ 1 * Y ρ 2 + (Y ρ 2) ^ 2 * b ^ 2
  change |κ ρ - k ρ| ≤ C * (b ^ 2 + H) / k ρ at Hval
  change |deriv κ ρ - deriv k ρ| ≤ C * D * (b ^ 2 + k ρ * H) at Hder
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity [hu.1, hv'.1]
  have hb0 : 0 ≤ b := add_nonneg hu.1.le hw.1
  have hb1 : b ≤ 1 := by dsimp only [b]; linarith only [hu.2, hw.2]
  have hb2 : b ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hb0 hb1 2
  have hV2 : (Y ρ 2) ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hv'.1.le hv'.2.le 2
  have hUV : Y ρ 1 * Y ρ 2 ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul (hu.2.trans (by norm_num)) hv'.2.le hv'.1.le (by norm_num)
      _ = _ := one_mul 1
  have hH : H ≤ 2 := by
    have Hprod : (Y ρ 2) ^ 2 * b ^ 2 ≤ 1 := by
      calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul hV2 hb2 (sq_nonneg _) (by norm_num)
        _ = _ := one_mul 1
    dsimp only [H]
    linarith only [hUV, Hprod]
  have Hvalue : |κ ρ - k ρ| ≤ B * a := Hval.trans (by
    calc
      _ ≤ C * (1 + 2) / k ρ := by gcongr
      _ ≤ C * (1 + 2) / (1 / (16 * a)) := div_le_div_of_nonneg_left (by positivity) (by positivity [ha.1]) hklo
      _ = (48 * C) * a := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBC ha.1.le)
  have Hderiv : |deriv κ ρ - deriv k ρ| ≤ B / a := Hder.trans (by
    calc
      _ ≤ C * D * (1 + k ρ * 2) := by gcongr
      _ ≤ C * D * (3 * k ρ) := by gcongr; linarith only [hk8]
      _ ≤ C * D * (3 * (32 / a)) := by gcongr
      _ = (96 * C * D) / a := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hBCD ha.1.le)
  have Hsmall : B / a ≤ 1 / (8192 * a ^ 2) := by
    have H := (le_div_iff₀ (by positivity : 0 < 8192 * B)).mp haB
    apply (div_le_div_iff₀ ha.1 (by positivity [ha.1] : 0 < 8192 * a ^ 2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right H ha.1.le]
  have Habs := abs_le.mp (Hderiv.trans Hsmall)
  obtain ⟨hκ6, hκ, _⟩ := entranceReturn_partialCore_entry hk8 hm.le ⟨hu.1.le, hu.2⟩ hv' hw
    ⟨hδ, hδsmall⟩ hsum
  change 99 / 100 * k ρ ≤ κ ρ ∧ κ ρ ≤ 101 / 100 * k ρ at hκ
  have Hκlo : 1 / (32 * a) ≤ κ ρ := by
    calc
      _ = (1 / 2) * (1 / (16 * a)) := by ring
      _ ≤ (1 / 2) * k ρ := mul_le_mul_of_nonneg_left hklo (by norm_num)
      _ ≤ _ := by linarith only [hκ.1, hkpos]
  have Hκhi : κ ρ ≤ 64 / a := by
    calc
      _ ≤ 2 * k ρ := by linarith only [hκ.2, hkpos]
      _ ≤ 2 * (32 / a) := mul_le_mul_of_nonneg_left hkhi (by norm_num)
      _ = _ := by ring
  refine ⟨Hκ, hκ6, Hκlo, Hκhi, Hvalue, Hderiv, ?_, ?_⟩
  · have heq : 1 / (4096 * a ^ 2) = 2 * (1 / (8192 * a ^ 2)) := by ring
    rw [heq] at Hklo
    linarith only [Habs.2, Hklo]
  · have Hunit : 1 / (8192 * a ^ 2) ≤ 1 / a ^ 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1]) (by nlinarith only [sq_nonneg a])
    have heq : 1536 / a ^ 2 + 1 / a ^ 2 = 1537 / a ^ 2 := by ring
    linarith only [Habs.1, Hkhi, Hunit, heq]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearEntrance_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η > (0 : ℝ),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
              let Z := fun t => entranceReturnState (Y t)
              let κ := fun t => coreRadius (Z t 0) (Z t 2)
              Y ρ 2 < 1 → DifferentiableAt ℝ Z ρ ∧ DifferentiableAt ℝ κ ρ ∧
              0 < -deriv κ ρ ∧ 0 < Z ρ 1 ∧ 0 < Z ρ 3 ∧
              |deriv (fun t => Z t 1) ρ| ≤ η * Real.sqrt (Z ρ 1) * |deriv κ ρ| ∧
              |deriv (fun t => Z t 3) ρ| ≤ η * Real.sqrt (Z ρ 3) * |deriv κ ρ| := by
  obtain ⟨C, hC, ε₀, hε₀, hε₀small, HC⟩ := exists_entrance_wall_sqrt_curve_bounds
  obtain ⟨hI, hhI, D, hD, HI⟩ := exists_restartShearEntrance_differential_inputs
  obtain ⟨hR, hhR, _, _, HR⟩ := exists_restartShearEntrance_radial_response
  refine ⟨min hI hR, lt_min hhI hhR, ?_⟩
  intro h hh q P hq hP η hη
  let E := 8388608 * C * D
  have hE : 0 < E := by dsimp only [E]; positivity
  let δ := min ε₀ ((η / E) ^ 2)
  have hδ : 0 < δ := lt_min hε₀ (sq_pos_of_pos (div_pos hη hE))
  have hδsmall : δ ≤ 1 / 10000 := (min_le_left _ _).trans hε₀small
  have hrootδ : Real.sqrt δ ≤ η / E := Real.sqrt_le_iff.mpr ⟨(div_pos hη hE).le, min_le_right _ _⟩
  have hEδ : E * Real.sqrt δ ≤ η := by
    have H := mul_le_mul_of_nonneg_left hrootδ hE.le
    simpa only [mul_div_cancel₀ _ hE.ne'] using H
  obtain ⟨aI, haI, HaI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aR, haR, HaR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aI aR, lt_min haI haR, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y Z κ hv
  obtain ⟨HY, hk8, _, hkhi, hm, hu, hv', hw, _, Hd0, Hdwall⟩ :=
    HaI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨HK, _, _, _, _, _, Hlo, _⟩ :=
    HaR a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let k := coreRadius (Y ρ 0) (Y ρ 2)
  change 8 ≤ k at hk8
  change k ≤ 32 / a at hkhi
  change 1 / (8192 * a ^ 2) ≤ -deriv κ ρ at Hlo
  have hk0 : 0 < k := by linarith only [hk8]
  have hk' : 7 / 4 ≤ coreRadius (Y ρ 0) (Y ρ 2) := by change 7 / 4 ≤ k; linarith only [hk8]
  obtain ⟨HZ, hU, hW, HU, HW⟩ := HC Y ρ D HY hD.le hk' hm.le
    ⟨hu.1, hu.2.trans (min_le_left _ _)⟩ hv' ⟨hw.1, hw.2.trans (min_le_left _ _)⟩ Hd0 Hdwall
  change |deriv (fun t => Z t 1) ρ| ≤ C * D * k ^ 2 * Real.sqrt (Y ρ 1 * Y ρ 2) * Real.sqrt (Z ρ 1) at HU
  change |deriv (fun t => Z t 3) ρ| ≤ C * D * k * Real.sqrt (Y ρ 3 * Y ρ 2) * Real.sqrt (Z ρ 3) at HW
  have Hratio : k ^ 2 ≤ 8388608 * |deriv κ ρ| := by
    calc
      _ ≤ (32 / a) ^ 2 := pow_le_pow_left₀ hk0.le hkhi 2
      _ = 8388608 * (1 / (8192 * a ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Hlo.trans (neg_le_abs _)) (by norm_num)
  have Hroot {w : ℝ} (hw : 0 ≤ w ∧ w ≤ δ) : Real.sqrt (w * Y ρ 2) ≤ Real.sqrt δ :=
    Real.sqrt_le_sqrt ((mul_le_of_le_one_right hw.1 hv'.2.le).trans hw.2)
  have Hwall {x dx w : ℝ} (hw : 0 ≤ w ∧ w ≤ δ)
      (H : |dx| ≤ C * D * k ^ 2 * Real.sqrt (w * Y ρ 2) * Real.sqrt x) :
      |dx| ≤ η * Real.sqrt x * |deriv κ ρ| := by
    calc
      _ ≤ C * D * k ^ 2 * Real.sqrt δ * Real.sqrt x := H.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Hroot hw) (by positivity)) (Real.sqrt_nonneg x))
      _ ≤ C * D * (8388608 * |deriv κ ρ|) * Real.sqrt δ * Real.sqrt x := by gcongr
      _ = (E * Real.sqrt δ) * Real.sqrt x * |deriv κ ρ| := by dsimp only [E]; ring
      _ ≤ _ := by gcongr
  have HW' : |deriv (fun t => Z t 3) ρ| ≤ C * D * k ^ 2 * Real.sqrt (Y ρ 3 * Y ρ 2) * Real.sqrt (Z ρ 3) := by
    apply HW.trans
    gcongr
    nlinarith only [mul_le_mul_of_nonneg_left (show 1 ≤ k by linarith only [hk8]) hk0.le]
  exact ⟨HZ, HK, (by positivity [ha.1] : 0 < 1 / (8192 * a ^ 2)).trans_le Hlo,
    hU, hW, Hwall ⟨hu.1.le, hu.2⟩ HU, Hwall ⟨hw.1.le, hw.2⟩ HW'⟩

end
end

/-- The exact shear family below the active-wall section reaches its fixed downward event
with negative radial slope and the full-core square-root cone margin. -/
theorem solution :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let Z := fun t => entranceReturnState (Y t)
            let κ := fun t => coreRadius (Z t 0) (Z t 2)
            let G := fun t => partialCoreDownwardReturnState (Y t)
            Y ρ 2 < 1 → 6 ≤ κ ρ ∧ DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ G ρ ∧
              deriv κ ρ < 0 ∧ deriv (fun t => G t 0) ρ < 0 ∧
              |deriv (fun t => G t 0) ρ / deriv κ ρ - 1| ≤ 1 / (32 * κ ρ) ∧
              (3 / 4 ≤ deriv (fun t => G t 0) ρ / deriv κ ρ ∧
                deriv (fun t => G t 0) ρ / deriv κ ρ ≤ 5 / 4) ∧
              ∀ i : Fin 2, |deriv (fun t => G t i.succ) ρ| ≤
                (1 - 1 / (16 * κ ρ)) * Real.sqrt (G ρ i.succ) * |deriv (fun t => G t 0) ρ| := by
  obtain ⟨δ, hδ, hδsmall, HC⟩ := exists_coreRadiusReturn_curve_cone
  obtain ⟨hI, hhI, _, _, HI⟩ := exists_restartShearEntrance_differential_inputs
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearEntrance_cone
  refine ⟨min hI hE, lt_min hhI hhE, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aI, haI, HaI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP 1 zero_lt_one
  refine ⟨min aI aE, lt_min haI haE, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y Z κ G hv
  obtain ⟨HY, hk8, _, _, hm, hu, hv', hw, hsmall, _⟩ :=
    HaI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨HZ, HK, Hneg, _, _, HU, HW⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  change DifferentiableAt ℝ Y ρ at HY
  change DifferentiableAt ℝ Z ρ at HZ
  change DifferentiableAt ℝ κ ρ at HK
  change 0 < -deriv κ ρ at Hneg
  change |deriv (fun t => Z t 1) ρ| ≤ 1 * Real.sqrt (Z ρ 1) * |deriv κ ρ| at HU
  change |deriv (fun t => Z t 3) ρ| ≤ 1 * Real.sqrt (Z ρ 3) * |deriv κ ρ| at HW
  have hu' : 0 ≤ Y ρ 1 ∧ Y ρ 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hδsmall⟩
  have hw' : 0 ≤ Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hδsmall⟩
  obtain ⟨hκ, _, hhit, _, _, hU, hW, hsum, _⟩ :=
    entranceReturn_partialCore_entry hk8 hm.le hu' hv' hw' ⟨hδ, hδsmall⟩ hsmall
  change 6 ≤ κ ρ at hκ
  change Z ρ 2 = 1 at hhit
  change Z ρ 1 + Z ρ 2 * Z ρ 3 ≤ δ / κ ρ at hsum
  rw [hhit, one_mul] at hsum
  let X : ℝ → CoreAngleState := fun t => ![κ t, Z t 1, Z t 3]
  have HX : DifferentiableAt ℝ X ρ := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i
    · exact HK
    · exact (differentiableAt_pi.mp HZ) 1
    · exact (differentiableAt_pi.mp HZ) 3
  have Hwall : ∀ i : Fin 2, |deriv (fun t => X t i.succ) ρ| ≤
      Real.sqrt (X ρ i.succ) * |deriv (fun t => X t 0) ρ| := by
    intro i
    fin_cases i
    · simpa [X] using HU
    · simpa [X] using HW
  have Hcore := HC X ρ HX hκ
    ⟨hU.1, (le_add_of_nonneg_right hW.1).trans hsum⟩
    ⟨hW.1, (le_add_of_nonneg_left hU.1).trans hsum⟩ (neg_pos.mp Hneg) Hwall
  let F := fun t => coreReturnState coreRadiusReturnTime (X t)
  have hg := (entrancePartialCore_fullCore_eventuallyEq hk8 hm.le hu' hv' hw'
    ⟨hδ, hδsmall⟩ hsmall).2
  have hk' : 7 / 4 ≤ coreRadius (Y ρ 0) (Y ρ 2) := by
    change 8 ≤ coreRadius (Y ρ 0) (Y ρ 2) at hk8
    linarith only [hk8]
  have hx := entranceReturn_coreCoordinates_eventuallyEq hk' hm.le hu' hv' hw'
  have heq : G =ᶠ[𝓝 ρ] F := by
    filter_upwards [HY.continuousAt.eventually hg, HY.continuousAt.eventually hx] with t ht hx'
    exact ht.trans (congrArg (coreReturnState coreRadiusReturnTime) hx')
  have heqi (i : Fin 3) : (fun t => G t i) =ᶠ[𝓝 ρ] fun t => F t i :=
    heq.mono fun _ h => congrFun h i
  refine ⟨hκ, HK, Hcore.1.congr_of_eventuallyEq heq, neg_pos.mp Hneg, ?_, ?_, ?_, ?_⟩
  · rw [(heqi 0).deriv_eq]
    exact Hcore.2.1
  · rw [(heqi 0).deriv_eq]
    exact Hcore.2.2.1
  · rw [(heqi 0).deriv_eq]
    exact Hcore.2.2.2.1
  · intro i
    rw [(heqi i.succ).deriv_eq, heq.self_of_nhds, (heqi 0).deriv_eq]
    exact Hcore.2.2.2.2 i
