-- Prove2me | solution 1 for BianchiIX.exists_restartPartialCore_radial_data
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:48:52.052814+00:00
-- url     : https://prove2.me/submissions/c4868bb6-393f-4f53-93ba-8375490e3ea6

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_arsinh_quotient_radial_derivative_bound
import Theorems.Thm_BianchiIX_exists_restartFastProjectionError_bounds
import Theorems.Thm_BianchiIX_exists_restartFastProjectiveEntry_bounds
import Theorems.Thm_BianchiIX_exists_restartRadialCurve_control
import Theorems.Thm_BianchiIX_exists_restartSection_radial_approximation
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_reciprocal_radial_bounds
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_restart_cutoff_budget (C C₀ q : ℝ) :
    ∀ᶠ ρ : ℝ in 𝓝[>] 0, (0 < ρ ∧ ρ ≤ 1) ∧ 2 * C₀ * ρ ≤ 1 / 16 ∧
      C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 := by
  have HI : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HL : Tendsto (fun ρ : ℝ => ρ * Real.log ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HB : Tendsto (fun ρ : ℝ => 2 * C₀ * ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using HI.const_mul (2 * C₀)
  have HT : Tendsto (fun ρ : ℝ => C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ))) (𝓝[>] 0) (𝓝 0) := by
    convert! HL.const_mul (-C * C₀ * q) using 1
    · ext ρ
      rw [one_div, Real.log_inv]
      ring
    · simp
  filter_upwards [show ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0 < ρ from self_mem_nhdsWithin,
    HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    HB.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    HT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with ρ hρ hρ1 hb ht
  exact ⟨⟨hρ, hρ1.le⟩, hb.le, ht.le⟩

end
end

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

private theorem BianchiIX.restartReferenceRoot_sq {n : ℝ} (hn : n ^ 2 ≤ 1) :
    restartReferenceRoot n ^ 2 = 1 - n ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hn)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.curvature_abs_le_sum_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |curvature a b c| ≤ (a + b + c) ^ 2 := by
  rw [abs_le]
  constructor
  · unfold curvature
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · unfold curvature
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

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
open Set Filter
open scoped Topology

private theorem BianchiIX.curvature_lower_of_active_dominance {n a b : ℝ} (ha : 0 < a)
    (hn : 0 ≤ n ∧ n ≤ a / 16) (hb : 0 ≤ b ∧ b ≤ a / 16) :
    3 / 4 * a ^ 2 ≤ curvature n a b := by
  have Hnb := mul_le_mul hn.2 hb.2 hb.1 (by positivity : 0 ≤ a / 16)
  have Hgap : 7 * a / 8 ≤ a - n - b := by linarith only [hn.2, hb.2]
  have Hsq := mul_self_le_mul_self (by positivity : 0 ≤ 7 * a / 8) Hgap
  unfold curvature
  nlinarith only [Hnb, Hsq]

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

private theorem BianchiIX.restartProjectionDefect_bounds {p : RestartRadialState} {r R : ℝ}
    (hr : 0 < r) (hp : ‖p‖ ≤ R) (ha : r / 2 ≤ p.2 1)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ p.2 1 / 16) (hb : 0 ≤ p.2 2 ∧ p.2 2 ≤ p.2 1 / 16) :
    3 * r ^ 2 / 16 ≤ restartProjectionDefect p ∧ restartProjectionDefect p ≤ 10 * R ^ 2 := by
  have ha0 : 0 < p.2 1 := by linarith only [ha, hr]
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have pn : |p.1| ≤ R := (norm_fst_le p).trans hp
  have pc (i : Fin 3) : |p.2 i| ≤ R := (norm_le_pi_norm p.2 i).trans ((norm_snd_le p).trans hp)
  constructor
  · have H := curvature_lower_of_active_dominance ha0 hn hb
    have Ha := pow_le_pow_left₀ (by positivity : 0 ≤ r / 2) ha 2
    dsimp only [restartProjectionDefect]
    nlinarith only [H, Ha, sq_nonneg (p.2 0)]
  · have H := (le_abs_self _).trans (curvature_abs_le_sum_sq hn.1 ha0.le hb.1)
    have Hs : (p.2 0) ^ 2 ≤ R ^ 2 := by nlinarith only [sq_abs (p.2 0), pow_le_pow_left₀ (abs_nonneg (p.2 0)) (pc 0) 2]
    have Hsum : p.1 + p.2 1 + p.2 2 ≤ 3 * R := by
      linarith only [(le_abs_self _).trans pn, (le_abs_self _).trans (pc 1), (le_abs_self _).trans (pc 2)]
    have Hsq := pow_le_pow_left₀ (add_nonneg (add_nonneg hn.1 ha0.le) hb.1) Hsum 2
    dsimp only [restartProjectionDefect]
    nlinarith only [H, Hs, Hsq]

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

private theorem BianchiIX.restartProjectionHeight_bounds {p : RestartRadialState} {r R : ℝ}
    (hr : 0 < r) (hp : ‖p‖ ≤ R) (hR : R ≤ 1 / 16) (ha : r / 2 ≤ p.2 1)
    (hn : 0 ≤ p.1 ∧ p.1 ≤ p.2 1 / 16) (hb : 0 ≤ p.2 2 ∧ p.2 2 ≤ p.2 1 / 16) :
    (0 ≤ restartProjectionDefect p ∧ restartProjectionDefect p ≤ 1 / 2) ∧
      r ^ 2 / 16 ≤ restartProjectionHeight p ∧ restartProjectionHeight p ≤ 10 * R ^ 2 := by
  obtain ⟨Hlo, Hhi⟩ := restartProjectionDefect_bounds hr hp ha hn hb
  have hd0 : 0 ≤ restartProjectionDefect p := le_trans (by positivity) Hlo
  have hd1 : restartProjectionDefect p ≤ 1 / 2 := by
    have HR := (norm_nonneg p).trans hp
    nlinarith only [Hhi, hR, HR]
  have hsqrt := Real.sqrt_nonneg (1 - restartProjectionDefect p)
  have hsqrt1 : Real.sqrt (1 - restartProjectionDefect p) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith only [hd0]
  have hden : 0 < 1 + Real.sqrt (1 - restartProjectionDefect p) := by positivity
  refine ⟨⟨hd0, hd1⟩, ?_, ?_⟩
  · apply (le_div_iff₀ hden).mpr
    have H := mul_le_mul_of_nonneg_left hsqrt1 (sq_nonneg r)
    nlinarith only [Hlo, H, sq_nonneg r]
  · apply (div_le_iff₀ hden).mpr
    nlinarith only [Hhi, mul_nonneg (sq_nonneg R) hsqrt]

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

private theorem BianchiIX.exists_restartFastEntry_control :
    ∃ C ≥ (32 : ℝ), ∀ h ∈ Ioc (0 : ℝ) (1 / (4 * C)),
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q → ∃ rstar : ℝ, 0 < rstar ∧
        ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) →
          ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let Z := restartRadialCurve θ ζ ρ
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
            let p := restartSectionRadialState h T Z
            let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
            r ≤ 1 ∧ 8 * (L + 1) * r ≤ 1 / 16 ∧ 0 ≤ T ∧
            0 < restartSectionRadicand h Z ∧ T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            stateConstraint x = 1 ∧ x 0 ≤ -(15 / 16) ∧
            HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ ∧
            0 < p.1 ∧ p.1 ≤ h * r ^ q ∧ ‖p‖ ≤ 8 * (L + 1) * r ∧ r / 2 ≤ p.2 1 ∧
            (0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ) ∧ p.1 ≤ p.2 1 / 16 ∧ p.2 2 ≤ p.2 1 / 16 ∧
            ‖v‖ ≤ 2 * (L + 1) ∧ |v.1| ≤ 2 * (L + 1) * p.1 / r ∧
            |v.2 2| ≤ 8 * C * (L + 1) * p.2 2 / r := by
  obtain ⟨C, hC, HC⟩ := exists_restartRadialCurve_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨C, hC, ?_⟩
  intro h hh L hL q hq
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    linarith only [H]
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.1.le]
  let M := 8 * (L + 1)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hL]
  have Hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ((0 < r ∧ r ≤ 1) ∧ M * r ≤ 1 / 16 ∧ C * (M * r) * (q / 2 * Real.log (1 / r)) ≤ 1 / 8) ∧
      r * (q / 2 * Real.log (1 / r)) ≤ 1 := by
    filter_upwards [eventually_restart_cutoff_budget C (4 * (L + 1)) q,
      eventually_restart_cutoff_budget 1 1 q] with r H₁ H₂
    have heq : 2 * (4 * (L + 1)) * r = M * r := by dsimp only [M]; ring
    rw [heq] at H₁
    exact ⟨H₁, by nlinarith only [H₂.2.2]⟩
  obtain ⟨r₀, hr₀, Hr₀⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hevent
  refine ⟨min r₀ (1 / 64), lt_min hr₀ (by norm_num), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have Hr := Hr₀ ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hrsmall : r ≤ 1 / 64 := hr.2.trans (min_le_right _ _)
  have hζsmall : 0 ≤ ζ ∧ ζ ≤ r / 9 := ⟨hζ.1, hζ.2.trans (by nlinarith only [hrsmall, hr.1])⟩
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq] : 0 ≤ q / 2)
    (Real.log_nonneg ((le_div_iff₀ hr.1).mpr (by linarith only [Hr.1.1.2])))
  obtain ⟨Hcurve, hneg, hnpos, hnexp, hcenter, hactive, hweak, hcv, hnv, hwv⟩ :=
    HC h r T L hh.1 hCh Hr.1.1 hL Hr.1.2.1 hT Hr.1.2.2 Hr.2 θ ζ ρ hθ hζsmall hρ
  change 0 < p.1 at hnpos
  change p.1 ≤ h * Real.exp (-2 * T) at hnexp
  change ‖p.2‖ ≤ M * r at hcenter
  change r / 2 ≤ p.2 1 at hactive
  change 0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ at hweak
  change ∀ i : Fin 3, |v.2 i| ≤ 2 * (L + 1) at hcv
  change |v.1| ≤ 2 * (L + 1) * p.1 / r at hnv
  have he : Real.exp (-2 * T) = r ^ q := by
    rw [Real.rpow_def_of_pos hr.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  rw [he] at hnexp
  have hpower : r ^ q ≤ r ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 Hr.1.1.2 hq.le
  have hnsmall : p.1 ≤ r ^ 2 := hnexp.trans
    ((mul_le_mul_of_nonneg_left hpower hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg r) (by linarith only [hhsmall])))
  have hnr : p.1 ≤ r := hnsmall.trans (by nlinarith only [hr.1, Hr.1.1.2])
  have hp : ‖p‖ ≤ M * r := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos hnpos]
    exact ⟨hnr.trans (by nlinarith only [mul_le_mul_of_nonneg_right hM hr.1.le]), hcenter⟩
  have hv : ‖v‖ ≤ 2 * (L + 1) := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    refine ⟨hnv.trans ?_, (pi_norm_le_iff_of_nonneg (by positivity)).mpr hcv⟩
    apply (div_le_iff₀ hr.1).mpr
    exact mul_le_mul_of_nonneg_left hnr (by positivity)
  have hZ := (restartRadialCurve_annulus hr.1 hρ hL hθ hζsmall).1
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh.1]) (by
      change ‖Z‖ ≤ 2 * (L + 1) * r at hZ
      have Hb : 8 * (L + 1) * r ≤ 1 / 16 := Hr.1.2.1
      linarith only [hZ, Hb])
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have hcon := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hrad.le) hT).2.1
  refine ⟨Hr.1.1.2, Hr.1.2.1, hT, hrad, hdom, hcon, hneg, Hcurve, hnpos, hnexp, hp,
    hactive, hweak, ?_, ?_, hv, hnv, hwv⟩
  · nlinarith only [hnsmall, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]
  · have Hw := hweak.2.trans (mul_le_mul_of_nonneg_left hζ.2 (by norm_num))
    nlinarith only [Hw, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]

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

private theorem BianchiIX.restartFastProjectionHeight_bounds {h T θ ζ ρ r R D : ℝ} {v : RestartRadialState}
    (hrad : 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ)) (hT : 0 ≤ T)
    (hneg : normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T 0 < 0)
    (H : HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ)
    (hr : 0 < r) (hp : ‖restartSectionRadialState h T (restartRadialCurve θ ζ ρ)‖ ≤ R)
    (hR : R ≤ 1 / 16)
    (ha : r / 2 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1)
    (hn : 0 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).1 ∧
      (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).1 ≤
        (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1 / 16)
    (hb : 0 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 2 ∧
      (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 2 ≤
        (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1 / 16)
    (hv : ‖v‖ ≤ D) :
    DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ ∧
      r ^ 2 / 16 ≤ restartFastProjectionHeight h T θ ζ ρ ∧
      restartFastProjectionHeight h T θ ζ ρ ≤ 10 * R ^ 2 ∧
      |deriv (restartFastProjectionHeight h T θ ζ) ρ| ≤ 32 * R * D := by
  obtain ⟨Hd, Hlo, Hhi⟩ := restartProjectionHeight_bounds hr hp hR ha hn hb
  have Hgerm := (eventually_restartSectionProjectionHeight_eq hrad hT hneg).comp_tendsto
    (hasDerivAt_restartRadialCurve θ ζ ρ).continuousAt
  change (fun y => restartProjectionHeight (restartSectionRadialState h T (restartRadialCurve θ ζ y))) =ᶠ[𝓝 ρ]
    restartFastProjectionHeight h T θ ζ at Hgerm
  have HD := restartProjectionHeight_derivative_bound H Hd.2 hp hv
  have Hactual := HD.1.hasDerivAt.congr_of_eventuallyEq Hgerm.symm
  rw [Hgerm.eq_of_nhds] at Hlo Hhi
  exact ⟨Hactual.differentiableAt, Hlo, Hhi, by rw [Hactual.deriv]; exact HD.2⟩

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

private theorem BianchiIX.coreAngle_toProjectiveState {x : NormalizedState} (hA : 1 + x 0 ≠ 0) :
    coreAngle (toProjectiveState x 0) (toProjectiveState x 2) =
      Real.arsinh (((1 + x 0) / Real.sqrt 3 - x 1) / x 3) := by
  change Real.arsinh ((1 - Real.sqrt 3 * x 1 / (1 + x 0)) /
    (Real.sqrt 3 * x 3 / (1 + x 0))) = _
  congr 1
  have hsqrt : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  by_cases ha : x 3 = 0
  · simp [ha]
  · field_simp

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
open Set

private theorem BianchiIX.differentiableAt_restartFastProjectiveEntry {h T θ ζ ρ : ℝ} {v : RestartRadialState}
    (H : HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ)
    (HA : DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ)
    (hA : restartFastProjectionHeight h T θ ζ ρ ≠ 0) :
    DifferentiableAt ℝ (restartFastProjectiveEntry h T θ ζ) ρ := by
  have Hn : DifferentiableAt ℝ (fun y => (restartSectionRadialState h T (restartRadialCurve θ ζ y)).1) ρ :=
    ((ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ H).differentiableAt
  have Hc (i : Fin 3) : DifferentiableAt ℝ
      (fun y => (restartSectionRadialState h T (restartRadialCurve θ ζ y)).2 i) ρ := by
    let P : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact (P.hasFDerivAt.comp_hasDerivAt ρ
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ H)).differentiableAt
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · exact ((Hc 0).const_mul (Real.sqrt 3)).div HA hA
  · exact (Hn.const_mul (Real.sqrt 3)).div HA hA
  · exact ((Hc 1).const_mul (Real.sqrt 3)).div HA hA
  · exact ((Hc 2).const_mul (Real.sqrt 3)).div HA hA

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartFastCoreAngle_derivative_bound {h T θ ζ ρ r M D : ℝ} {v : RestartRadialState}
    (H : HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ)
    (HA : DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ)
    (hr : 0 < r) (hM : 0 ≤ M) (hD : 0 ≤ D) (hsmall : M * r ≤ 1 / 16)
    (hp : ‖restartSectionRadialState h T (restartRadialCurve θ ζ ρ)‖ ≤ M * r)
    (hv : ‖v‖ ≤ D)
    (ha : r / 2 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1)
    (hA : 0 < restartFastProjectionHeight h T θ ζ ρ)
    (hAhi : restartFastProjectionHeight h T θ ζ ρ ≤ 10 * (M * r) ^ 2)
    (hAd : |deriv (restartFastProjectionHeight h T θ ζ) ρ| ≤ 32 * (M * r) * D) :
    DifferentiableAt ℝ (restartFastCoreAngle h T θ ζ) ρ ∧
      |deriv (restartFastCoreAngle h T θ ζ) ρ| ≤ 20 * M * D / r := by
  let P := fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)
  let A := restartFastProjectionHeight h T θ ζ
  let f := fun y => A y / Real.sqrt 3 - (P y).2 0
  let a := fun y => (P y).2 1
  change 0 < A ρ at hA
  have Hc (i : Fin 3) : HasDerivAt (fun y => (P y).2 i) (v.2 i) ρ := by
    let Q : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact Q.hasFDerivAt.comp_hasDerivAt ρ
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ H)
  have Hpc (i : Fin 3) : |(P ρ).2 i| ≤ M * r :=
    (norm_le_pi_norm (P ρ).2 i).trans ((norm_snd_le (P ρ)).trans hp)
  have Hvc (i : Fin 3) : |v.2 i| ≤ D :=
    (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have HAr : A ρ ≤ M * r := by
    have Hsmall := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hM hr.le)
    change A ρ ≤ 10 * (M * r) ^ 2 at hAhi
    nlinarith only [hAhi, Hsmall, mul_nonneg hM hr.le]
  have HAd : |deriv A ρ| ≤ 2 * D := hAd.trans (by
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hD])
  have Hf : HasDerivAt f (deriv A ρ / Real.sqrt 3 - v.2 0) ρ :=
    (HA.hasDerivAt.div_const (Real.sqrt 3)).sub (Hc 0)
  have Hfval : |f ρ| ≤ 2 * M * r := by
    have Htriangle := abs_sub_le (A ρ / Real.sqrt 3) 0 ((P ρ).2 0)
    simp only [sub_zero, zero_sub, abs_neg, abs_of_pos (div_pos hA hsqrt)] at Htriangle
    have HAs := (div_le_self hA.le hsqrt1).trans HAr
    change |A ρ / Real.sqrt 3 - (P ρ).2 0| ≤ _
    linarith only [Htriangle, HAs, Hpc 0]
  have Hfder : |deriv A ρ / Real.sqrt 3 - v.2 0| ≤ 3 * D := by
    have Htriangle := abs_sub_le (deriv A ρ / Real.sqrt 3) 0 (v.2 0)
    simp only [sub_zero, zero_sub, abs_neg, abs_div, abs_of_pos hsqrt] at Htriangle
    have HAs := (div_le_self (abs_nonneg (deriv A ρ)) hsqrt1).trans HAd
    linarith only [Htriangle, HAs, Hvc 0]
  have Hangle := arsinh_quotient_radial_derivative_bound Hf (Hc 1) hr hM hD Hfval
    ⟨ha, (le_abs_self _).trans (Hpc 1)⟩ Hfder (Hvc 1)
  have Hgerm : restartFastCoreAngle h T θ ζ =ᶠ[𝓝 ρ] (fun y => Real.arsinh (f y / a y)) := by
    filter_upwards [HA.continuousAt.eventually (isOpen_Ioi.mem_nhds hA)] with y hy
    exact coreAngle_toProjectiveState (ne_of_gt hy)
  have HD := Hangle.1.hasDerivAt.congr_of_eventuallyEq Hgerm
  exact ⟨HD.differentiableAt, by rw [HD.deriv]; exact Hangle.2⟩

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
open Set

private theorem BianchiIX.exists_restartFastEntry_radial_response :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h T θ ζ
            let p := fun y => Y y 2 * Y y 3
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ Y ρ ∧ DifferentiableAt ℝ (restartFastCoreAngle h T θ ζ) ρ ∧
            |deriv (restartFastCoreAngle h T θ ζ) ρ| ≤ K / r ∧
            (∀ i : Fin 3, 0 ≤ Y ρ i.succ ∧
              |deriv (fun y => Y y i.succ) ρ| ≤ K * Y ρ i.succ / r) ∧
            DifferentiableAt ℝ p ρ ∧ 0 ≤ p ρ ∧ |deriv p ρ| ≤ K * p ρ / r ∧
            0 < Y ρ 1 ∧ DifferentiableAt ℝ (fun y => Real.log (Y y 1)) ρ ∧
            |deriv (fun y => Real.log (Y y 1)) ρ| ≤ K / r ∧
            (0 < ζ → 0 < p ρ ∧ DifferentiableAt ℝ (fun y => Real.log (p y)) ρ ∧
              |deriv (fun y => Real.log (Y y 1)) ρ| + |deriv (fun y => Real.log (p y)) ρ| ≤ K / r) ∧
            (ζ = 0 → Y ρ 3 = 0 ∧ deriv (fun y => Y y 3) ρ = 0 ∧ p ρ = 0 ∧ deriv p ρ = 0) := by
  obtain ⟨C, hC, HC⟩ := exists_restartFastEntry_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  intro h hh L hL
  let M := 8 * (L + 1)
  let D := 2 * (L + 1)
  let E := 8 * C * (L + 1)
  let F := 512 * M * D
  let B := E + F
  let K := 3 * B + 20 * M * D
  have hM : 0 < M := by dsimp only [M]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hE : 0 < E := by dsimp only [E]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  have hB : 0 < B := add_pos hE hF
  have hK : 0 < K := by dsimp only [K]; positivity
  have hDE : 2 * D ≤ E := by
    dsimp only [D, E]
    nlinarith only [hL, mul_le_mul_of_nonneg_right hC (show 0 ≤ L + 1 by positivity)]
  have hBK : B ≤ K := by dsimp only [K]; nlinarith only [hB, mul_pos hM hD]
  have h2BK : B + B ≤ K := by dsimp only [K]; nlinarith only [hB, mul_pos hM hD]
  have h3BK : 3 * B ≤ K := by dsimp only [K]; nlinarith only [mul_pos hM hD]
  have hAK : 20 * M * D ≤ K := by dsimp only [K]; linarith only [hB]
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨rstar, hrstar, HR⟩ := HC h hh L hL q hq
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let P := fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
  let A := restartFastProjectionHeight h T θ ζ
  let Y := restartFastProjectiveEntry h T θ ζ
  let p := fun y => Y y 2 * Y y 3
  obtain ⟨_, hsmall, hT, hrad, hdom, _, hneg, Hcurve, hnpos, _, hp, ha, hb, hnsmall, hbsmall, hv, hnv, hwv⟩ :=
    HR r hr θ ζ hθ hζ ρ hρ
  change HasDerivAt P v ρ at Hcurve
  change ‖P ρ‖ ≤ M * r at hp
  change ‖v‖ ≤ D at hv
  change 0 < (P ρ).1 at hnpos
  change r / 2 ≤ (P ρ).2 1 at ha
  change 0 ≤ (P ρ).2 2 ∧ (P ρ).2 2 ≤ 2 * ζ at hb
  change |v.1| ≤ D * (P ρ).1 / r at hnv
  change |v.2 2| ≤ E * (P ρ).2 2 / r at hwv
  obtain ⟨HAD, HAlo, HAhi, HAd⟩ := restartFastProjectionHeight_bounds hrad hT
    (by linarith only [hneg]) Hcurve hr.1 hp hsmall ha ⟨hnpos.le, hnsmall⟩ ⟨hb.1, hbsmall⟩ hv
  change DifferentiableAt ℝ A ρ at HAD
  change r ^ 2 / 16 ≤ A ρ at HAlo
  change A ρ ≤ 10 * (M * r) ^ 2 at HAhi
  change |deriv A ρ| ≤ 32 * (M * r) * D at HAd
  have hA : 0 < A ρ := lt_of_lt_of_le (by positivity [hr.1]) HAlo
  have HArel : |deriv A ρ| ≤ F * A ρ / r := by
    apply (le_div_iff₀ hr.1).mpr
    have Hlo := mul_le_mul_of_nonneg_left HAlo hF.le
    have Hhi := mul_le_mul_of_nonneg_right HAd hr.1.le
    dsimp only [F] at Hlo ⊢
    nlinarith only [Hlo, Hhi]
  have Hn : HasDerivAt (fun y => (P y).1) v.1 ρ :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ Hcurve
  have Hc (i : Fin 3) : HasDerivAt (fun y => (P y).2 i) (v.2 i) ρ := by
    let Q : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact Q.hasFDerivAt.comp_hasDerivAt ρ
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ Hcurve)
  have Hvc (i : Fin 3) : |v.2 i| ≤ D := (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have ha0 : 0 < (P ρ).2 1 := by linarith only [ha, hr.1]
  have Hnrel : |v.1| ≤ E * (P ρ).1 / r := hnv.trans (by
    apply div_le_div_of_nonneg_right _ hr.1.le
    apply mul_le_mul_of_nonneg_right _ hnpos.le
    linarith only [hDE, hD])
  have Harel : |v.2 1| ≤ E * (P ρ).2 1 / r := (Hvc 1).trans (by
    apply (le_div_iff₀ hr.1).mpr
    have H₁ := mul_le_mul_of_nonneg_left ha hD.le
    have H₂ := mul_le_mul_of_nonneg_right hDE ha0.le
    nlinarith only [H₁, H₂])
  have HU := scaled_quotient_radial_derivative_bound Hn HAD.hasDerivAt hr.1
    (Real.sqrt_nonneg (3 : ℝ)) hnpos.le hA Hnrel HArel
  have HV := scaled_quotient_radial_derivative_bound (Hc 1) HAD.hasDerivAt hr.1
    (Real.sqrt_nonneg (3 : ℝ)) ha0.le hA Harel HArel
  have HW := scaled_quotient_radial_derivative_bound (Hc 2) HAD.hasDerivAt hr.1
    (Real.sqrt_nonneg (3 : ℝ)) hb.1 hA hwv HArel
  change DifferentiableAt ℝ (fun y => Y y 1) ρ ∧ |deriv (fun y => Y y 1) ρ| ≤ B * Y ρ 1 / r at HU
  change DifferentiableAt ℝ (fun y => Y y 2) ρ ∧ |deriv (fun y => Y y 2) ρ| ≤ B * Y ρ 2 / r at HV
  change DifferentiableAt ℝ (fun y => Y y 3) ρ ∧ |deriv (fun y => Y y 3) ρ| ≤ B * Y ρ 3 / r at HW
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hu : 0 < Y ρ 1 := div_pos (mul_pos hsqrt hnpos) hA
  have hvpos : 0 < Y ρ 2 := div_pos (mul_pos hsqrt ha0) hA
  have hw : 0 ≤ Y ρ 3 := div_nonneg (mul_nonneg hsqrt.le hb.1) hA.le
  have HP := product_radial_derivative_bound HV.1 HW.1 hvpos.le hw HV.2 HW.2
  change DifferentiableAt ℝ p ρ ∧ |deriv p ρ| ≤ (B + B) * p ρ / r at HP
  have hprod : 0 ≤ p ρ := mul_nonneg hvpos.le hw
  have HlogU := log_radial_derivative_bound HU.1 hu HU.2
  have HYD := differentiableAt_restartFastProjectiveEntry Hcurve HAD (ne_of_gt hA)
  have Hangle := restartFastCoreAngle_derivative_bound Hcurve HAD hr.1 hM.le hD.le hsmall hp hv ha hA HAhi HAd
  have Hwalls : ∀ i : Fin 3, 0 ≤ Y ρ i.succ ∧
      |deriv (fun y => Y y i.succ) ρ| ≤ K * Y ρ i.succ / r := by
    intro i
    fin_cases i
    · exact ⟨hu.le, HU.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBK hu.le) hr.1.le)⟩
    · exact ⟨hvpos.le, HV.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBK hvpos.le) hr.1.le)⟩
    · exact ⟨hw, HW.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBK hw) hr.1.le)⟩
  refine ⟨hdom, HYD, Hangle.1, Hangle.2.trans (div_le_div_of_nonneg_right hAK hr.1.le),
    Hwalls, HP.1, hprod, HP.2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2BK hprod) hr.1.le), hu, HlogU.1,
    HlogU.2.trans (div_le_div_of_nonneg_right hBK hr.1.le), ?_, ?_⟩
  · intro hζpos
    have hinit : positiveWalls (restartSectionChart h Z) := ⟨hh.1, hr.1.trans_le hρ.1, hζpos⟩
    have Hpos := (normalizedMaxCurve_forward hinit (restartSectionChart_constraint hrad.le) hT).2.1
    have hwpos : 0 < Y ρ 3 := div_pos (mul_pos hsqrt Hpos.2.2) hA
    have hppos : 0 < p ρ := mul_pos hvpos hwpos
    have HlogP := log_radial_derivative_bound HP.1 hppos HP.2
    refine ⟨hppos, HlogP.1, ?_⟩
    calc
      _ ≤ B / r + (B + B) / r := add_le_add HlogU.2 HlogP.2
      _ = 3 * B / r := by ring
      _ ≤ K / r := div_le_div_of_nonneg_right h3BK hr.1.le
  · intro hζzero
    have Hb0 : (P ρ).2 2 = 0 := by rw [hζzero] at hb; linarith only [hb.1, hb.2]
    have Hw0 : Y ρ 3 = 0 := by
      change Real.sqrt 3 * (P ρ).2 2 / A ρ = 0
      rw [Hb0]
      simp
    have Hp0 : p ρ = 0 := by change Y ρ 2 * Y ρ 3 = 0; rw [Hw0, mul_zero]
    refine ⟨Hw0, ?_, Hp0, ?_⟩
    · exact abs_nonpos_iff.mp (by simpa only [Hw0, mul_zero, zero_div] using HW.2)
    · exact abs_nonpos_iff.mp (by simpa only [Hp0, mul_zero, zero_div] using HP.2)

end
end

/-- A common scale for the exact fast entrance and all ordinary radial data used at its return. -/
theorem solution :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 1 ≤ K ∧ ∃ D : ℝ, 0 < D ∧
        ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let k := restartFastCoreRadius h s θ ζ
            let z := restartFastCoreAngle h s θ ζ
            let Z := Real.arsinh (4 * (8 * (L + 1)))
            r ≤ 1 ∧ 0 ≤ s ∧ 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ) ∧
            s ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            0 < restartFastProjectionHeight h s θ ζ ρ ∧ DifferentiableAt ℝ Y ρ ∧
            0 ≤ Z ∧ max 6 (2 * Real.cosh Z) ≤ k ρ ∧ z ρ ≤ Z ∧
            coreRegion (k ρ) (Y ρ) ∧ 1 < Y ρ 2 ∧ Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ 1 / k ρ ∧
            2 / (K * r) ≤ k ρ ∧ k ρ ≤ K / r ∧ |deriv k ρ| ≤ K / r ^ 2 ∧
            1 / (D * r ^ 2) ≤ -deriv k ρ ∧
            |deriv (fun a => Y a 1) ρ| ≤ K * Y ρ 1 / r ∧
            |deriv (fun a => Y a 2 * Y a 3) ρ| ≤ K * (Y ρ 2 * Y ρ 3) / r ∧
            |deriv z ρ| ≤ K / r := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_entry
  obtain ⟨hR, hhR, HR⟩ := exists_restartFastCoreRadius_bounds
  obtain ⟨hD, hhD, HD⟩ := exists_restartFastEntry_radial_response
  refine ⟨min hE (min hR hD), lt_min hhE (lt_min hhR hhD), ?_⟩
  intro h hh L hL
  have hhE' : h ∈ Ioc (0 : ℝ) hE := ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  have hhR' : h ∈ Ioc (0 : ℝ) hR :=
    ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩
  have hhD' : h ∈ Ioc (0 : ℝ) hD :=
    ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩
  obtain ⟨D, hDpos, HDD⟩ := HD h hhD' L hL
  let B := 8 * (L + 1) + 1
  let J := 512 * (2 * L + 4)
  let K := 1 + B + 32 + J + D
  have hB : 0 < B := by dsimp only [B]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith only [hB, hJ, hDpos]
  have hBK : B ≤ K := by dsimp only [K]; linarith only [hJ, hDpos]
  have h32K : 32 ≤ K := by dsimp only [K]; linarith only [hB, hJ, hDpos]
  have hJK : J ≤ K := by dsimp only [K]; linarith only [hB, hDpos]
  have hDK : D ≤ K := by dsimp only [K]; linarith only [hB, hJ]
  refine ⟨K, hK, 4 * B ^ 2, by positivity, ?_⟩
  intro q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rE, hrE, HEE⟩ := HE h hhE' L hL q P hq hP (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨rR, hrR, HRR⟩ := HR h hhR' L hL q hq2
  obtain ⟨rD, hrD, HDD'⟩ := HDD q hq2
  refine ⟨min rE (min rR (min rD 1)), lt_min hrE (lt_min hrR (lt_min hrD (by norm_num))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrE' : r ∈ Ioc (0 : ℝ) rE := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hrR' : r ∈ Ioc (0 : ℝ) rR :=
    ⟨hr.1, (hr.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩
  have hrD1 := ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _))
  have hrD' : r ∈ Ioc (0 : ℝ) rD := ⟨hr.1, hrD1.trans (min_le_left _ _)⟩
  have hr1 : r ≤ 1 := hrD1.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1
      (by linarith only [hP] : (2 : ℝ) ≤ P)
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let k := restartFastCoreRadius h s θ ζ
  obtain ⟨hs, hrad, hdom, hA, hk6, hangle, _, _, _, hsum, hV, _, hregion⟩ := HEE r hrE' θ ζ hθ hζ ρ hρ
  obtain ⟨_, _, _, hklo, hkhi, hdklo, hdkhi⟩ := HRR r hrR' θ ζ hθ hζ2 ρ hρ
  obtain ⟨_, hY, _, hdz, hw, _, hp, hdp, _⟩ := HDD' r hrD' θ ζ hθ hζ2 ρ hρ
  change 2 / (B * r) ≤ k ρ at hklo
  change k ρ ≤ 32 / r at hkhi
  change 1 / (4 * B ^ 2 * r ^ 2) ≤ -deriv k ρ at hdklo
  change -deriv k ρ ≤ J / r ^ 2 at hdkhi
  have hdk0 : deriv k ρ ≤ 0 := by
    have H : 0 ≤ 1 / (4 * B ^ 2 * r ^ 2) := by positivity
    linarith only [H, hdklo]
  have hdk : |deriv k ρ| ≤ K / r ^ 2 := by
    rw [abs_of_nonpos hdk0]
    exact hdkhi.trans (div_le_div_of_nonneg_right hJK (sq_nonneg r))
  have hklo' : 2 / (K * r) ≤ k ρ := le_trans
    (div_le_div_of_nonneg_left (by norm_num) (mul_pos hB hr.1)
      (mul_le_mul_of_nonneg_right hBK hr.1.le)) hklo
  have hkhi' : k ρ ≤ K / r := hkhi.trans (div_le_div_of_nonneg_right h32K hr.1.le)
  have hU := hw 0
  change 0 ≤ Y ρ 1 ∧ |deriv (fun a => Y a 1) ρ| ≤ D * Y ρ 1 / r at hU
  have hdU : |deriv (fun a => Y a 1) ρ| ≤ K * Y ρ 1 / r :=
    hU.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hDK hU.1) hr.1.le)
  have hdp' : |deriv (fun a => Y a 2 * Y a 3) ρ| ≤ K * (Y ρ 2 * Y ρ 3) / r :=
    hdp.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hDK hp) hr.1.le)
  have hdz' : |deriv (restartFastCoreAngle h s θ ζ) ρ| ≤ K / r :=
    hdz.trans (div_le_div_of_nonneg_right hDK hr.1.le)
  have hkpos : 0 < k ρ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) ((le_max_left _ _).trans hk6)
  have hsum' : Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ 1 / k ρ :=
    hsum.trans (div_le_div_of_nonneg_right (by norm_num) hkpos.le)
  exact ⟨hr1, hs, hrad, hdom, hA, hY, Real.arsinh_nonneg_iff.mpr (by positivity),
    hk6, hangle.2, hregion, lt_of_lt_of_le (by norm_num) hV, hsum',
    hklo', hkhi', hdk, hdklo, hdU, hdp', hdz'⟩
