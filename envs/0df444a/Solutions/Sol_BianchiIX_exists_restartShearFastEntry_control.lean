-- Prove2me | solution 1 for BianchiIX.exists_restartShearFastEntry_control
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:46:30.854749+00:00
-- url     : https://prove2.me/submissions/8f3c44b3-fa19-4eef-a74c-c82099c6aac3

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_exists_restartSectionMixedFlow_derivative
import Theorems.Thm_BianchiIX_exists_restartSectionRemainder_bounds
import Theorems.Thm_BianchiIX_exists_restartSectionWeakWall_derivative
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_clock
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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
open Set Filter
open scoped Topology

private theorem BianchiIX.restart_cutoff_scale_bounds {C C₀ h ρ q : ℝ}
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hh : 0 ≤ h) (hρ : 0 < ρ ∧ ρ ≤ 1) (hq : 1 ≤ q) :
    (4 * C * C₀ ^ 2 * ρ ^ 2 * (q / 2 * Real.log (1 / ρ)) + 6 * h * C₀ * ρ ^ (q + 1) ≤
      (2 * C * C₀ ^ 2 * q + 6 * h * C₀) * ρ ^ 2 * (1 + |Real.log ρ|)) ∧
    (8 * C * C₀ * ρ * (q / 2 * Real.log (1 / ρ)) + 6 * h * ρ ^ q ≤
      (4 * C * C₀ * q + 6 * h) * ρ * (1 + |Real.log ρ|)) := by
  have hρ0 : 0 < ρ := hρ.1
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hlog : Real.log (1 / ρ) = |Real.log ρ| := by
    rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hρ0.le hρ.2)]
  have hp2 : ρ ^ (q + 1) ≤ ρ ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hρ0 hρ.2
      (by linarith only [hq] : (2 : ℝ) ≤ q + 1)
  have hp1 : ρ ^ q ≤ ρ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hρ0 hρ.2 hq
  constructor
  · have H := mul_le_mul_of_nonneg_left hp2 (by positivity : 0 ≤ 6 * h * C₀)
    have Hextra : 0 ≤ (2 * C * C₀ ^ 2 * q) * ρ ^ 2 + (6 * h * C₀) * ρ ^ 2 * |Real.log ρ| := by positivity
    rw [hlog]
    nlinarith only [H, Hextra]
  · have H := mul_le_mul_of_nonneg_left hp1 (by positivity : 0 ≤ 6 * h)
    have Hextra : 0 ≤ (4 * C * C₀ * q) * ρ + (6 * h) * ρ * |Real.log ρ| := by positivity
    rw [hlog]
    nlinarith only [H, Hextra]

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

private theorem BianchiIX.restartCenterTransfer_apply (n : ℝ) (v : RestartCenterState) :
    restartCenterTransfer n v = ![
      restartShearFactor n * v 0 + restartShearCoupling n * (v 1 - v 2),
      restartWallFactor n * v 1, restartWallFactor n * v 2] := by
  ext i
  fin_cases i <;> rfl

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

private theorem BianchiIX.restartCenterTransfer_sub_id_bound {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) :
    ‖restartCenterTransfer n - ContinuousLinearMap.id ℝ RestartCenterState‖ ≤ 3 * n := by
  obtain ⟨ha0, ha1, hc0, hc1, hk0, hk1⟩ := restart_coefficients_small hn
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [hn.1])
  intro v
  have hv (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hdiff : |v 1 - v 2| ≤ 2 * ‖v‖ := by
    have H := abs_sub_le (v 1) 0 (v 2)
    simp only [sub_zero, zero_sub, abs_neg] at H
    linarith only [H, hv 1, hv 2]
  have hw (i : Fin 3) : |(restartWallFactor n - 1) * v i| ≤ n * ‖v‖ := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul hc1 (hv i) (abs_nonneg _) hn.1
  apply (pi_norm_le_iff_of_nonneg (by positivity [hn.1] : 0 ≤ 3 * n * ‖v‖)).mpr
  intro i
  rw [sub_apply, ContinuousLinearMap.id_apply, restartCenterTransfer_apply]
  fin_cases i
  · change |restartShearFactor n * v 0 + restartShearCoupling n * (v 1 - v 2) - v 0| ≤ _
    rw [show restartShearFactor n * v 0 + restartShearCoupling n * (v 1 - v 2) - v 0 =
      (restartShearFactor n - 1) * v 0 + restartShearCoupling n * (v 1 - v 2) by ring]
    calc
      _ ≤ |(restartShearFactor n - 1) * v 0| + |restartShearCoupling n * (v 1 - v 2)| := abs_add_le _ _
      _ ≤ n * ‖v‖ + n * (2 * ‖v‖) := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hk0]
        exact add_le_add (mul_le_mul ha1 (hv 0) (abs_nonneg _) hn.1)
          (mul_le_mul hk1 hdiff (abs_nonneg _) hn.1)
      _ = _ := by ring
  · change |restartWallFactor n * v 1 - v 1| ≤ _
    rw [← sub_one_mul]
    exact (hw 1).trans (by nlinarith only [mul_nonneg hn.1 (norm_nonneg v)])
  · change |restartWallFactor n * v 2 - v 2| ≤ _
    rw [← sub_one_mul]
    exact (hw 2).trans (by nlinarith only [mul_nonneg hn.1 (norm_nonneg v)])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restart_negative_branch_root {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    -x 0 = Real.sqrt (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) := by
  have hr : 1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4) = x 0 ^ 2 := by
    dsimp only [stateConstraint, constraint, shearSq] at hc
    linarith only [hc]
  rw [hr, Real.sqrt_sq_eq_abs, abs_of_neg hp]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_restartRadicand (k : WithTop ℕ∞) : ContDiff ℝ k restartRadicand := by
  unfold restartRadicand curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartCompactRoot {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactRoot x :=
  (contDiff_restartRadicand k).contDiffAt.sqrt hx.ne'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartCompactField {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactField x := by
  have hr := contDiffAt_restartCompactRoot hx k
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> dsimp [restartCompactField, restartCompactWeakRate, shearMinus, curvature] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_restartCompactField_zero : HasFDerivAt (𝕜 := ℝ) restartCompactField 0 0 := by
  have hp (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i (0 : RestartState)
  have hQ : HasFDerivAt (𝕜 := ℝ) (fun x : RestartState => curvature (x 0) (x 2) (x 3)) 0 0 := by
    have H := (((hp 0).pow 2).add ((hp 2).pow 2) |>.add ((hp 3).pow 2)).sub
      ((((hp 0).mul (hp 2)).add ((hp 2).mul (hp 3)) |>.add ((hp 3).mul (hp 0))).const_mul 2)
    convert! H using 1
    simp
  have hR : HasFDerivAt (𝕜 := ℝ) restartRadicand 0 0 := by
    convert! (((hp 1).pow 2).const_sub 1).sub hQ using 1
    simp
  have hr : HasFDerivAt (𝕜 := ℝ) restartCompactRoot 0 0 := by
    convert! hR.sqrt (by norm_num [restartRadicand, curvature] : restartRadicand 0 ≠ 0) using 1
    simp
  have hH : HasFDerivAt (𝕜 := ℝ) (fun x : RestartState => -(x 2) ^ 2 + (x 3) ^ 2 + x 0 * x 2 - x 0 * x 3) 0 0 := by
    convert! ((((hp 2).pow 2).neg.add ((hp 3).pow 2)).add ((hp 0).mul (hp 2))).sub
      ((hp 0).mul (hp 3)) using 1
    simp
  have hg (ε : ℝ) := ((hQ.sub_const 1).add hr).add ((hp 1).const_mul (ε * Real.sqrt 3))
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert! (hQ.sub_const 1).sub (hr.const_mul 2) using 1
    simp
  · convert! (hQ.mul (hp 1)).add (hH.const_mul (Real.sqrt 3)) using 1
    simp [curvature]
  · convert! (hp 2).mul (hg 1) using 1
    simp [curvature, restartCompactRoot, restartRadicand]
  · convert! (hp 3).mul (hg (-1)) using 1
    simp [curvature, restartCompactRoot, restartRadicand]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartCompactField_fderiv_zero : fderiv ℝ restartCompactField 0 = 0 :=
  hasFDerivAt_restartCompactField_zero.fderiv

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
open Set

private theorem BianchiIX.exists_restartCompact_derivative_bounds :
    ∃ C ≥ (1 : ℝ), ∀ x : RestartState, ‖x‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartCompactField x‖ ≤ C * ‖x‖ ∧
        ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖ ≤ C := by
  let S := Metric.closedBall (0 : RestartState) (1 / 16)
  have hreg (x : RestartState) (hx : x ∈ S) : ContDiffAt ℝ 3 restartCompactField x := by
    have H := (restartCompact_box_bounds (by simpa [S] using hx)).2.1
    exact contDiffAt_restartCompactField (by linarith only [H]) 3
  have hq : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖) S := by
    intro x hx
    exact (((hreg x hx).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : RestartState) (1 / 16)).exists_bound_of_continuousOn hq
  let C := max B 1
  have hbound (x : RestartState) (hx : x ∈ S) :
      ‖fderiv ℝ (fderiv ℝ restartCompactField) x‖ ≤ C := by
    exact (le_abs_self _).trans ((hB x hx).trans (le_max_left B 1))
  have hdiff (x : RestartState) (hx : x ∈ S) : DifferentiableAt ℝ (fderiv ℝ restartCompactField) x :=
    ((hreg x hx).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx
  have hxS : x ∈ S := by simpa [S] using hx
  have hzS : (0 : RestartState) ∈ S := by simp [S]
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (convex_closedBall (0 : RestartState) (1 / 16)) hzS hxS
  exact ⟨by simpa only [restartCompactField_fderiv_zero, sub_zero] using H, hbound x hxS⟩

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
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

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

private theorem BianchiIX.restartCompactCenterProjection_norm_le (x : RestartState) :
    ‖restartCompactCenterProjection x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm x 1
  · exact norm_le_pi_norm x 2
  · exact norm_le_pi_norm x 3

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
open Set

private theorem BianchiIX.restartCompactField_physical {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) :
    restartCompactField (restartPhysicalCoordinates x) 0 = rateOne (x 0) (x 1) ∧
      restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x)) =
        restartCenterProjection (normalizedField x) := by
  have hroot := restart_negative_branch_root hc hp
  have hq : curvature (x 2) (x 3) (x 4) = 1 - shearSq (x 0) (x 1) := by
    dsimp only [stateConstraint, constraint] at hc
    linarith only [hc]
  constructor
  · change curvature (x 2) (x 3) (x 4) - 1 - 2 * Real.sqrt
      (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) = _
    rw [← hroot, hq]
    dsimp only [rateOne]
    ring
  · ext i
    fin_cases i
    · rfl
    · change x 3 * (curvature (x 2) (x 3) (x 4) - 1 + Real.sqrt
        (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) + 1 * Real.sqrt 3 * x 1) =
        rateTwo (x 0) (x 1) * x 3
      rw [← hroot, hq]
      dsimp only [rateTwo]
      ring
    · change x 4 * (curvature (x 2) (x 3) (x 4) - 1 + Real.sqrt
        (1 - x 1 ^ 2 - curvature (x 2) (x 3) (x 4)) + (-1) * Real.sqrt 3 * x 1) =
        rateThree (x 0) (x 1) * x 4
      rw [← hroot, hq]
      dsimp only [rateThree]
      ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartPhysical_shear_bound {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0)
    (hx : ‖restartPhysicalCoordinates x‖ ≤ 1 / 16) : x 0 ≤ -(15 / 16) := by
  have H := (restartCompact_box_bounds hx).2.2.2.1
  have heq : restartCompactRoot (restartPhysicalCoordinates x) = -x 0 :=
    (restart_negative_branch_root hc hp).symm
  rw [heq] at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCenterField_bound {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    {x : NormalizedState} (hc : stateConstraint x = 1) (hp : x 0 < 0)
    (hn : 0 ≤ x 2 ∧ x 2 ≤ 1 / 16) (hZ : ‖restartCenterProjection x‖ ≤ 1 / 16) :
    ‖restartCenterProjection (normalizedField x)‖ ≤
      C * (x 2 + ‖restartCenterProjection x‖) * ‖restartCenterProjection x‖ := by
  let r := ‖restartCenterProjection x‖
  let R := max (x 2) r
  let w : RestartState := ![x 2, 0, 0, 0]
  let S := Metric.closedBall (0 : RestartState) R
  have hR : 0 ≤ R := hn.1.trans (le_max_left _ _)
  have hRsmall : R ≤ 1 / 16 := max_le hn.2 hZ
  have hRsum : R ≤ x 2 + r := max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left hn.1)
  have hxS : restartPhysicalCoordinates x ∈ S := by
    simpa [S] using restartPhysicalCoordinates_norm_le hR
      (by simpa only [abs_of_nonneg hn.1] using le_max_left (x 2) r) (le_max_right (x 2) r)
  have hwS : w ∈ S := by
    change ‖w - 0‖ ≤ R
    rw [sub_zero]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    fin_cases i
    · change |x 2| ≤ R
      rw [abs_of_nonneg hn.1]
      exact le_max_left _ _
    all_goals simpa [w] using hR
  have hdiff (z : RestartState) (hz : z ∈ S) : DifferentiableAt ℝ restartCompactField z := by
    have hzR : ‖z‖ ≤ R := by simpa [S] using hz
    have H := (restartCompact_box_bounds (hzR.trans hRsmall)).2.1
    exact (contDiffAt_restartCompactField (by linarith only [H]) 1).differentiableAt (by norm_num)
  have hbound (z : RestartState) (hz : z ∈ S) : ‖fderiv ℝ restartCompactField z‖ ≤ C * R := by
    have hzR : ‖z‖ ≤ R := by simpa [S] using hz
    exact (hF z (hzR.trans hRsmall)).trans (mul_le_mul_of_nonneg_left hzR hC)
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_closedBall (0 : RestartState) R) hwS hxS
  have hdist : ‖restartPhysicalCoordinates x - w‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (restartCenterProjection x))).mpr
    intro i
    fin_cases i
    · change |x 2 - x 2| ≤ r
      simpa only [sub_self, abs_zero] using norm_nonneg (restartCenterProjection x)
    · change |x 1 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 0
    · change |x 3 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 1
    · change |x 4 - 0| ≤ r
      rw [sub_zero]
      exact norm_le_pi_norm (restartCenterProjection x) 2
  have hzero : restartCompactCenterProjection (restartCompactField w) = 0 := by
    ext i
    fin_cases i <;> simp [restartCompactCenterProjection, restartCompactField, w, shearMinus]
  rw [← (restartCompactField_physical hc hp).2]
  have heq : restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x)) =
      restartCompactCenterProjection (restartCompactField (restartPhysicalCoordinates x) - restartCompactField w) := by
    rw [map_sub, hzero, sub_zero]
  rw [heq]
  exact (restartCompactCenterProjection_norm_le _).trans
    (H.trans ((mul_le_mul_of_nonneg_left hdist (mul_nonneg hC hR)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRsum hC) (norm_nonneg _))))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartFastBudget (C h b t : ℝ) :
    HasDerivAt (restartFastBudget C h b) (C * (h * Real.exp (-2 * t) + b)) t := by
  convert! (((((hasDerivAt_id' t).const_mul (-2)).exp.const_sub 1).const_mul (h / 2)).add
    ((hasDerivAt_id' t).const_mul b)).const_mul C using 1
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastBudget_zero (C h b : ℝ) : restartFastBudget C h b 0 = 0 := by
  simp [restartFastBudget]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartFastBudget_le {C h b T t : ℝ} (hC : 0 ≤ C) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (ht : t ≤ T) : restartFastBudget C h b t ≤ C * h / 2 + C * b * T := by
  have H := mul_nonneg (mul_nonneg hC hh) (Real.exp_pos (-2 * t)).le
  have Ht := mul_le_mul_of_nonneg_left ht (mul_nonneg hC hb)
  dsimp only [restartFastBudget]
  nlinarith only [H, Ht]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exp_one_quarter_lt_two : Real.exp (1 / 4 : ℝ) < 2 := by
  have H := Real.exp_lt_two_add_div_two_sub (x := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  norm_num at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restart_fastLayer_prefix {C h b T : ℝ} {α : ℝ → NormalizedState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 2 * h ≤ 1 / 16) (hb : b ≤ 1 / 16)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 < α t 2)
    (hregion : ∀ t ∈ Icc (0 : ℝ) T, restartControlRegion h b (α t))
    (hinit : α 0 2 ≤ h) :
    ∀ t ∈ Icc (0 : ℝ) T,
      α t 2 ≤ h * Real.exp (-2 * t) ∧ α t 0 ≤ -(15 / 16) ∧
        ‖restartCenterProjection (α t)‖ ≤
          ‖restartCenterProjection (α 0)‖ * Real.exp (restartFastBudget C h b t) := by
  have hbox (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖restartPhysicalCoordinates (α t)‖ ≤ 1 / 16 :=
    restartPhysicalCoordinates_norm_le (by norm_num)
      (by rw [abs_of_pos (hn t ht)]; exact (hregion t ht).2.1.trans hh) ((hregion t ht).2.2.trans hb)
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 0 < 0 := by
    have H := (hregion t ht).1
    linarith only [H]
  have hdecay (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 2 ≤ h * Real.exp (-2 * t) := by
    have HD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :=
      (hasDerivAt_normalized_components (hα s ⟨hs.1, hs.2.trans ht.2⟩)).2.2.1
    have HB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
        rateOne (α s 0) (α s 1) * α s 2 ≤ -2 * α s 2 := by
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      have H := (restartCompact_box_bounds (hbox s hsT)).2.2.2.2.2.2
      rw [(restartCompactField_physical (hc s hsT) (hp s hsT)).1] at H
      exact mul_le_mul_of_nonneg_right H.le (hn s hsT).le
    have H := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) t) HD HB
      (s := 0) (t := t) ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
    have H' : α t 2 ≤ α 0 2 * Real.exp (-2 * t) := by simpa only [sub_zero] using H
    exact H'.trans (mul_le_mul_of_nonneg_right hinit (Real.exp_pos _).le)
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun s => restartCenterProjection (α s))
        (restartCenterProjection (normalizedField (α t))) t := by
    convert! restartCenterProjection.hasFDerivAt.comp_hasDerivAt t (hα t ht) using 1
  have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖restartCenterProjection (normalizedField (α t))‖ ≤
        (C * (h * Real.exp (-2 * t) + b)) * ‖restartCenterProjection (α t)‖ := by
    have H := restartCenterField_bound hC hF (hc t ht) (hp t ht)
      ⟨(hn t ht).le, (hregion t ht).2.1.trans hh⟩ ((hregion t ht).2.2.trans hb)
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add (hdecay t ht) (hregion t ht).2.2) hC) (norm_nonneg _))
  have HG := norm_le_exp_of_norm_deriv_clock HD (fun t _ => hasDerivAt_restartFastBudget C h b t) HB
  intro t ht
  refine ⟨hdecay t ht, restartPhysical_shear_bound (hc t ht) (hp t ht) (hbox t ht), ?_⟩
  simpa only [restartFastBudget_zero, sub_zero] using HG t ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isClosed_restartControlRegion (h b : ℝ) : IsClosed {x | restartControlRegion h b x} :=
  (isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le (continuous_apply 2) continuous_const).inter
      (isClosed_le restartCenterProjection.continuous.norm continuous_const))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_restart_fastLayer_control {C h b T : ℝ} {x : NormalizedState}
    (hC : 0 ≤ C)
    (hF : ∀ w : RestartState, ‖w‖ ≤ 1 / 16 → ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖)
    (hh : 0 < h ∧ h ≤ 1 / 128) (hb : 0 < b ∧ b ≤ 1 / 16) (_hT : 0 ≤ T)
    (hbudget : C * h / 2 + C * b * T ≤ 1 / 4)
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hn : 0 < x 2 ∧ x 2 ≤ h)
    (hZ : ‖restartCenterProjection x‖ ≤ b / 2) :
    ∀ t ∈ Icc (0 : ℝ) T,
      let y := normalizedMaxCurve x 0 t
      0 < y 2 ∧ y 2 ≤ h * Real.exp (-2 * t) ∧ y 0 ≤ -(15 / 16) ∧
        ‖restartCenterProjection y‖ ≤ ‖restartCenterProjection x‖ * Real.exp (restartFastBudget C h b t) ∧
        ‖restartCenterProjection y‖ < b := by
  let α := normalizedMaxCurve x 0
  let S := {t : ℝ | restartControlRegion h b (α t)}
  have hα (t : ℝ) (ht : 0 ≤ t) : HasDerivAt α (normalizedField (α t)) t :=
    (normalizedMaxCurve_forward_of_constraint hc ht).1
  have hcon (t : ℝ) (ht : 0 ≤ t) : stateConstraint (α t) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc ht).2.1
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < α t 2 := by
    have H := normalizedMaxCurve_wall_sign hc ht (0 : Fin 3)
    change (α t 2 = 0 ↔ x 2 = 0) ∧ (0 ≤ α t 2 ↔ 0 ≤ x 2) at H
    have hne : α t 2 ≠ 0 := fun he => hn.1.ne' (H.1.mp he)
    exact lt_of_le_of_ne (H.2.mpr hn.1.le) hne.symm
  have hinit : α 0 = x := normalizedMaxCurve_initial x 0
  have hhsmall : 2 * h ≤ 1 / 16 := by linarith only [hh.2]
  have hZsmall : ‖restartCenterProjection x‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
  have hpx : x 0 ≤ -(15 / 16) := restartPhysical_shear_bound hc hp
    (restartPhysicalCoordinates_norm_le (by norm_num)
      (by rw [abs_of_pos hn.1]; linarith only [hn.2, hh.2]) hZsmall)
  have hS0 : (0 : ℝ) ∈ S := by
    change restartControlRegion h b (α 0)
    rw [hinit]
    exact ⟨by linarith only [hpx], by linarith only [hn.2, hh.1], by linarith only [hZ, hb.1]⟩
  have hclosed : IsClosed (S ∩ Icc 0 T) := by
    have H := (HasDerivAt.continuousOn (fun t (ht : t ∈ Icc (0 : ℝ) T) => hα t ht.1)).preimage_isClosed_of_isClosed
      isClosed_Icc (isClosed_restartControlRegion h b)
    convert! H using 1
    ext t
    change (restartControlRegion h b (α t) ∧ t ∈ Icc 0 T) ↔
      (t ∈ Icc 0 T ∧ restartControlRegion h b (α t))
    tauto
  have hstrict {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
      (HZ : ‖restartCenterProjection (α t)‖ ≤
        ‖restartCenterProjection (α 0)‖ * Real.exp (restartFastBudget C h b t)) :
      ‖restartCenterProjection (α t)‖ < b := by
    rw [hinit] at HZ
    have HE := (restartFastBudget_le hC hh.1.le hb.1.le ht.2).trans hbudget
    have hbhalf : 0 < b / 2 := div_pos hb.1 (by norm_num)
    have H := HZ.trans (mul_le_mul hZ (Real.exp_le_exp.mpr HE) (Real.exp_pos _).le hbhalf.le)
    have H' := mul_lt_mul_of_pos_left exp_one_quarter_lt_two hbhalf
    nlinarith only [H, H']
  have hwhole : Icc (0 : ℝ) T ⊆ S := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hS0
    intro t ht hbefore
    have H := restart_fastLayer_prefix hC hF hhsmall hb.2
      (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hpos u hu.1)
      (fun u hu => hbefore hu) (by rw [hinit]; exact hn.2) t ⟨ht.1, le_rfl⟩
    have hpstrict : α t 0 < -(1 / 2) := by linarith only [H.2.1]
    have hnstrict : α t 2 < 2 * h := by
      have he := Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)
      have Hn := H.1.trans (mul_le_mul_of_nonneg_left he hh.1.le)
      nlinarith only [Hn, hh.1]
    have hZstrict := hstrict ⟨ht.1, ht.2.le⟩ H.2.2
    have hpcont := (continuous_apply (0 : Fin 5)).continuousAt.comp (hα t ht.1).continuousAt
    have hncont := (continuous_apply (2 : Fin 5)).continuousAt.comp (hα t ht.1).continuousAt
    have hZcont := (restartCenterProjection.continuous.continuousAt.comp (hα t ht.1).continuousAt).norm
    have Hev : ∀ᶠ u in 𝓝 t, u ∈ S := by
      filter_upwards [hpcont.eventually (isOpen_Iio.mem_nhds hpstrict),
        hncont.eventually (isOpen_Iio.mem_nhds hnstrict),
        hZcont.eventually (isOpen_Iio.mem_nhds hZstrict)] with u hpu hnu hZu
      exact ⟨hpu.le, hnu.le, hZu.le⟩
    exact Hev.filter_mono nhdsWithin_le_nhds
  have H := restart_fastLayer_prefix hC hF hhsmall hb.2
    (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hpos u hu.1)
    (fun u hu => hwhole hu) (by rw [hinit]; exact hn.2)
  intro t ht
  have Ht := H t ht
  refine ⟨hpos t ht.1, Ht.1, Ht.2.1, ?_, hstrict ht Ht.2.2⟩
  simpa only [hinit] using Ht.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_normalized_restart_fastLayer_control :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (x : NormalizedState),
      (0 < h ∧ h ≤ 1 / 128) → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T →
      C * h / 2 + C * b * T ≤ 1 / 4 → stateConstraint x = 1 → x 0 < 0 →
      (0 < x 2 ∧ x 2 ≤ h) → ‖restartCenterProjection x‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        let y := normalizedMaxCurve x 0 t
        0 < y 2 ∧ y 2 ≤ h * Real.exp (-2 * t) ∧ y 0 ≤ -(15 / 16) ∧
          ‖restartCenterProjection y‖ ≤ ‖restartCenterProjection x‖ * Real.exp (restartFastBudget C h b t) ∧
          ‖restartCenterProjection y‖ < b := by
  obtain ⟨A, _, HA⟩ := exists_restartCompact_derivative_bounds
  let C := max A 32
  have hC : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) (le_max_right A 32)
  have hF (w : RestartState) (hw : ‖w‖ ≤ 1 / 16) : ‖fderiv ℝ restartCompactField w‖ ≤ C * ‖w‖ :=
    (HA w hw).1.trans (mul_le_mul_of_nonneg_right (le_max_left A 32) (norm_nonneg w))
  exact ⟨C, le_max_right _ _, fun _ _ _ _ => normalized_restart_fastLayer_control hC hF⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSection_fastLayer_control :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T →
      C * b * T ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        let x := normalizedMaxCurve (restartSectionChart h Z) 0 t
        0 < x 2 ∧ x 2 ≤ h * Real.exp (-2 * t) ∧ x 0 ≤ -(15 / 16) ∧
          ‖restartSectionCenterFlow h t Z‖ ≤ ‖Z‖ * Real.exp (restartFastBudget C h b t) ∧
          ‖restartSectionCenterFlow h t Z‖ < b := by
  obtain ⟨C, hC, HC⟩ := exists_normalized_restart_fastLayer_control
  refine ⟨C, hC, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ
  have hhsmall : h ≤ 1 / 128 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  let w : RestartState := ![h, Z 0, Z 1, Z 2]
  have hw : ‖w‖ ≤ 1 / 16 := by
    have hZsmall : ‖Z‖ ≤ 1 / 16 := by linarith only [hZ, hb.2]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr
    intro i
    fin_cases i
    · change |h| ≤ 1 / 16
      rw [abs_of_pos hh]
      linarith only [hhsmall]
    · exact (norm_le_pi_norm Z 0).trans hZsmall
    · exact (norm_le_pi_norm Z 1).trans hZsmall
    · exact (norm_le_pi_norm Z 2).trans hZsmall
  have hr : 0 < restartSectionRadicand h Z := by
    have H := (restartCompact_box_bounds hw).2.1
    change 246 / 256 ≤ restartSectionRadicand h Z at H
    linarith only [H]
  have hp : restartSectionChart h Z 0 < 0 := neg_lt_zero.mpr (Real.sqrt_pos.mpr hr)
  have hbudget : C * h / 2 + C * b * T ≤ 1 / 4 := by linarith only [hCh, hCb]
  have H := HC h b T (restartSectionChart h Z) ⟨hh, hhsmall⟩ hb hT hbudget
    (restartSectionChart_constraint hr.le) hp ⟨hh, le_rfl⟩
    (by simpa only [restartCenterProjection_section] using hZ)
  intro t ht
  simpa only [restartCenterProjection_section, restartSectionCenterFlow] using H t ht

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSection_fastLayer_cutoff :
    ∃ C ≥ (32 : ℝ), ∀ (h b ρ q : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) →
      (0 < ρ ∧ ρ ≤ 1) → 0 ≤ q →
      C * b * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      let T := q / 2 * Real.log (1 / ρ)
      let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
      0 < x 2 ∧ x 2 ≤ h * ρ ^ q ∧ x 0 ≤ -(15 / 16) ∧
        ‖restartSectionCenterFlow h T Z‖ ≤ ‖Z‖ * Real.exp (1 / 4) ∧
        ‖restartSectionCenterFlow h T Z‖ < b := by
  obtain ⟨C, hC, HC⟩ := exists_restartSection_fastLayer_control
  refine ⟨C, hC, ?_⟩
  intro h b ρ q Z hh hCh hb hρ hq hCb hZ
  let T := q / 2 * Real.log (1 / ρ)
  change C * b * T ≤ 1 / 8 at hCb
  have hlog : 0 ≤ Real.log (1 / ρ) :=
    Real.log_nonneg ((le_div_iff₀ hρ.1).mpr (by linarith only [hρ.2]))
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hq (by norm_num)) hlog
  have he : Real.exp (-2 * T) = ρ ^ q := by
    rw [Real.rpow_def_of_pos hρ.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  have H := HC h b T Z hh hCh hb hT hCb hZ T ⟨hT, le_rfl⟩
  have hbudget : restartFastBudget C h b T ≤ 1 / 4 :=
    (restartFastBudget_le (by linarith only [hC]) hh.le hb.1.le le_rfl).trans
      (by linarith only [hCh, hCb])
  refine ⟨H.1, ?_, H.2.2.1, ?_, H.2.2.2.2⟩
  · simpa only [he] using H.2.1
  · exact H.2.2.2.1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbudget) (norm_nonneg Z))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartMixedChart_section {h : ℝ} (hh : 0 < h) (Z : RestartCenterState) :
    restartMixedChart (restartMixedSection h Z) = restartSectionChart h Z := by
  ext i
  fin_cases i <;> simp [restartMixedChart, restartMixedSection, restartSectionChart,
    restartCompactRoot, restartRadicand, restartExpCoordinates, restartSectionRadicand, Real.exp_log hh]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionMixedFlow_physical {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartSectionMixedFlow h t Z =
      restartMixedCoordinates (normalizedMaxCurve (restartSectionChart h Z) 0 t) := by
  rw [restartSectionMixedFlow, restartMixedFlow, restartMixedChart_section hh]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionMixedFlow_center {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartCompactCenterProjection (restartSectionMixedFlow h t Z) = restartSectionCenterFlow h t Z := by
  rw [restartSectionMixedFlow_physical hh]
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartCompactCenterProjection_comp_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] RestartState) :
    ‖restartCompactCenterProjection.comp L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro v
  exact (restartCompactCenterProjection_norm_le (L v)).trans (L.le_opNorm v)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_restartSectionCenterFlow_of_mixed {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionCenterFlow h t)
      (restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) Z := by
  have H := restartCompactCenterProjection.hasFDerivAt.comp Z HD.hasFDerivAt
  simpa only [Function.comp_def, restartSectionMixedFlow_center hh] using H

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

private theorem BianchiIX.contDiffAt_restartSectionStrongWall {h t : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z)
    (ht : t ∈ normalizedMaxDomain (restartSectionChart h Z) 0) :
    ContDiffAt ℝ 2 (restartSectionStrongWall h t) Z := by
  have H : ContDiffAt ℝ 2
      (fun W => normalizedMaxCurve (restartSectionChart h W) 0 t) Z :=
    (contDiffAt_normalizedMaxCurve_two ht).comp Z
      (g := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2)
      ((contDiffAt_restartSectionChart hZ 2).prodMk (contDiffAt_const (c := t)))
  exact (contDiffAt_apply ℝ ℝ (2 : Fin 5) _).comp Z H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongWall_pos {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 ≤ restartSectionRadicand h Z) (ht : 0 ≤ t) :
    0 < restartSectionStrongWall h t Z := by
  have H := normalizedMaxCurve_wall_sign (restartSectionChart_constraint hZ) ht (0 : Fin 3)
  change (restartSectionStrongWall h t Z = 0 ↔ h = 0) ∧
    (0 ≤ restartSectionStrongWall h t Z ↔ 0 ≤ h) at H
  have hne : restartSectionStrongWall h t Z ≠ 0 := fun he => hh.ne' (H.1.mp he)
  exact lt_of_le_of_ne (H.2.mpr hh.le) hne.symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongLog_eq {h : ℝ} (hh : 0 < h) (t : ℝ) (Z : RestartCenterState) :
    restartSectionStrongLog h t Z = restartSectionMixedFlow h t Z 0 := by
  rw [restartSectionMixedFlow_physical hh]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_restartSectionStrongLog {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionStrongLog h t)
      ((ContinuousLinearMap.proj (0 : Fin 4)).comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) Z := by
  have H := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) (restartSectionMixedFlow h t Z)).comp Z HD.hasFDerivAt
  convert! H using 1
  ext W
  exact restartSectionStrongLog_eq hh t W

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongLog_fderiv_norm_le {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    ‖fderiv ℝ (restartSectionStrongLog h t) Z‖ ≤ ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ := by
  rw [(hasFDerivAt_restartSectionStrongLog hh HD).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (norm_le_pi_norm (fderiv ℝ (restartSectionMixedFlow h t) Z v) 0).trans
    ((fderiv ℝ (restartSectionMixedFlow h t) Z).le_opNorm v)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_restartSectionStrongWall {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    HasFDerivAt (restartSectionStrongWall h t)
      (restartSectionStrongWall h t Z • fderiv ℝ (restartSectionStrongLog h t) Z) Z := by
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hZ.le) 0 ht
  have hn := restartSectionStrongWall_pos hh hZ.le ht
  have Hlog := (hasFDerivAt_restartSectionStrongLog hh HD).differentiableAt.hasFDerivAt
  have HE := Hlog.exp
  have heq : (fun W => Real.exp (restartSectionStrongLog h t W)) =ᶠ[𝓝 Z] restartSectionStrongWall h t := by
    filter_upwards [(contDiffAt_restartSectionStrongWall hZ hdom).continuousAt.eventually
      (isOpen_Ioi.mem_nhds hn)] with W hW
    exact Real.exp_log hW
  have H := HE.congr_of_eventuallyEq heq.symm
  simpa only [restartSectionStrongLog, Real.exp_log hn] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionStrongWall_fderiv_norm {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z) :
    ‖fderiv ℝ (restartSectionStrongWall h t) Z‖ =
      restartSectionStrongWall h t Z * ‖fderiv ℝ (restartSectionStrongLog h t) Z‖ := by
  rw [(hasFDerivAt_restartSectionStrongWall hh hZ ht HD).fderiv, norm_smul, Real.norm_eq_abs,
    abs_of_pos (restartSectionStrongWall_pos hh hZ.le ht)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSection_cutoff_remainder :
    ∃ C ≥ (32 : ℝ), ∀ (h C₀ ρ q : ℝ),
      0 < h → C * h ≤ 1 / 4 → 0 < C₀ → (0 < ρ ∧ ρ ≤ 1) → 0 ≤ q →
      2 * C₀ * ρ ≤ 1 / 16 → C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 →
      ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ →
        let T := q / 2 * Real.log (1 / ρ)
        let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
        T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
        0 < x 2 ∧ x 2 ≤ h * ρ ^ q ∧
        restartSectionCenterFlow h T Z = restartCenterTransfer h Z + restartSectionRemainder h T Z ∧
        DifferentiableAt ℝ (restartSectionRemainder h T) Z ∧
        ‖restartSectionRemainder h T Z‖ ≤ 4 * C * C₀ ^ 2 * ρ ^ 2 * T + 6 * h * C₀ * ρ ^ (q + 1) ∧
        ‖fderiv ℝ (restartSectionRemainder h T) Z‖ ≤ 8 * C * C₀ * ρ * T + 6 * h * ρ ^ q := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionRemainder_bounds
  obtain ⟨B, _, HB⟩ := exists_restartSection_fastLayer_cutoff
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 32) hA
  have hC0 : 0 ≤ C := hA0.trans hAC
  refine ⟨C, hA.trans hAC, ?_⟩
  intro h C₀ ρ q hh hCh hC₀ hρ hq hb hCb Z hZ
  have hρ0 : 0 < ρ := hρ.1
  let b := 2 * C₀ * ρ
  let T := q / 2 * Real.log (1 / ρ)
  have hb0 : 0 < b := by dsimp only [b]; positivity
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hq (by norm_num))
    (Real.log_nonneg ((le_div_iff₀ hρ.1).mpr (by linarith only [hρ.2])))
  have hZb : ‖Z‖ ≤ b / 2 := by dsimp only [b]; linarith only [hZ]
  have HAh : A * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hAC hh.le).trans hCh
  have HBh : B * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hBC hh.le).trans hCh
  have HAT : A * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hb0.le) hT).trans hCb
  have HBT : B * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hb0.le) hT).trans hCb
  have HR := HA h b T hh HAh ⟨hb0, hb⟩ hT HAT T ⟨hT, le_rfl⟩ Z hZb
  have Hn := HB h b ρ q Z hh HBh ⟨hb0, hb⟩ hρ hq HBT hZb
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right (hA.trans hAC) hh.le]
  have hrad := restartSectionRadicand_pos_of_small
    (by rwa [abs_of_pos hh]) (by linarith only [hZ, hb] : ‖Z‖ ≤ 1 / 16)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have he : Real.exp (-2 * T) = ρ ^ q := by
    rw [Real.rpow_def_of_pos hρ.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  rw [he] at HR
  refine ⟨hdom, Hn.1, Hn.2.1, ?_, HR.1, ?_, ?_⟩
  · dsimp only [restartSectionRemainder]
    abel
  · apply HR.2.1.trans
    have H1 : 4 * A * T * ‖Z‖ ^ 2 ≤ 4 * C * T * (C₀ * ρ) ^ 2 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAC (by norm_num)) hT)
        ((sq_le_sq₀ (norm_nonneg Z) (mul_pos hC₀ hρ0).le).mpr hZ)
        (sq_nonneg _) (by positivity)
    have H2 : 6 * h * ρ ^ q * ‖Z‖ ≤ 6 * h * ρ ^ q * (C₀ * ρ) := by
      exact mul_le_mul_of_nonneg_left hZ (by positivity)
    exact (add_le_add H1 H2).trans_eq (by rw [Real.rpow_add hρ0, Real.rpow_one]; ring)
  · apply HR.2.2.trans
    have H1 : 8 * A * T * ‖Z‖ ≤ 8 * C * T * (C₀ * ρ) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAC (by norm_num)) hT)
        hZ (norm_nonneg _) (by positivity)
    calc
      8 * A * T * ‖Z‖ + 6 * h * ρ ^ q ≤ 8 * C * T * (C₀ * ρ) + 6 * h * ρ ^ q :=
        add_le_add H1 le_rfl
      _ = 8 * C * C₀ * ρ * T + 6 * h * ρ ^ q := by ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_restartSection_linear_approximation :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ C₀ : ℝ, 0 < C₀ → ∀ q : ℝ, 2 < q →
        ∃ K : ℝ, 0 < K ∧ ∃ ρstar : ℝ, 0 < ρstar ∧
          ∀ ρ ∈ Ioc (0 : ℝ) ρstar, ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ →
            let T := q / 2 * Real.log (1 / ρ)
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
            T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            0 < x 2 ∧ x 2 ≤ h * ρ ^ q ∧
            restartSectionCenterFlow h T Z = restartCenterTransfer h Z + restartSectionRemainder h T Z ∧
            DifferentiableAt ℝ (restartSectionRemainder h T) Z ∧
            ‖restartSectionRemainder h T Z‖ ≤ K * ρ ^ 2 * (1 + |Real.log ρ|) ∧
            ‖fderiv ℝ (restartSectionRemainder h T) Z‖ ≤ K * ρ * (1 + |Real.log ρ|) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSection_cutoff_remainder
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  let hstar := 1 / (4 * C)
  have hstarpos : 0 < hstar := by dsimp only [hstar]; positivity
  refine ⟨hstar, hstarpos, ?_⟩
  intro h hh C₀ hC₀ q hq
  have hhpos : 0 < h := hh.1
  have hq0 : 0 < q := by linarith only [hq]
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    nlinarith only [H]
  let KV := 2 * C * C₀ ^ 2 * q + 6 * h * C₀
  let KD := 4 * C * C₀ * q + 6 * h
  let K := max KV KD
  have hKD : 0 < KD := by dsimp only [KD]; positivity
  have hK : 0 < K := hKD.trans_le (le_max_right _ _)
  obtain ⟨ρstar, hρstar, Hbudget⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_cutoff_budget C C₀ q)
  refine ⟨K, hK, ρstar, hρstar, ?_⟩
  intro ρ hρ Z hZ
  have Hb := Hbudget hρ
  have HR := HC h C₀ ρ q hhpos hCh hC₀ Hb.1 hq0.le Hb.2.1 Hb.2.2 Z hZ
  have HS := restart_cutoff_scale_bounds hCpos.le hC₀.le hhpos.le Hb.1
    (by linarith only [hq] : (1 : ℝ) ≤ q)
  obtain ⟨Hdom, Hpos, Hwall, Hdecomp, Hdiff, Hvalue, Hderiv⟩ := HR
  refine ⟨Hdom, Hpos, Hwall, Hdecomp, Hdiff, ?_, ?_⟩
  · apply Hvalue.trans (HS.1.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left KV KD) (sq_nonneg ρ)) (by positivity)
  · apply Hderiv.trans (HS.2.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right KV KD) hρ.1.le) (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartSectionRadialState_derivative {h t : ℝ} {Z : RestartCenterState}
    (hh : 0 < h) (hZ : 0 < restartSectionRadicand h Z) (ht : 0 ≤ t)
    (HD : DifferentiableAt ℝ (restartSectionMixedFlow h t) Z)
    (HB : ‖fderiv ℝ (restartSectionMixedFlow h t) Z‖ ≤ 2)
    (hn : restartSectionStrongWall h t Z ≤ 1) :
    DifferentiableAt ℝ (restartSectionRadialState h t) Z ∧
      ‖fderiv ℝ (restartSectionRadialState h t) Z‖ ≤ 2 ∧
      ∀ v : RestartCenterState,
        |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤
          2 * restartSectionStrongWall h t Z * ‖v‖ := by
  have Hn := hasFDerivAt_restartSectionStrongWall hh hZ ht HD
  have HZ := hasFDerivAt_restartSectionCenterFlow_of_mixed hh HD
  have HP := Hn.prodMk HZ
  change HasFDerivAt (restartSectionRadialState h t) _ Z at HP
  have hnpos := restartSectionStrongWall_pos hh hZ.le ht
  have Hlog := (restartSectionStrongLog_fderiv_norm_le hh HD).trans HB
  have hnD : ‖fderiv ℝ (restartSectionStrongWall h t) Z‖ ≤ 2 * restartSectionStrongWall h t Z := by
    rw [restartSectionStrongWall_fderiv_norm hh hZ ht HD]
    nlinarith only [mul_le_mul_of_nonneg_left Hlog hnpos.le]
  have hZD : ‖fderiv ℝ (restartSectionCenterFlow h t) Z‖ ≤ 2 := by
    rw [HZ.fderiv]
    exact (restartCompactCenterProjection_comp_norm_le _).trans HB
  have hfst (v : RestartCenterState) :
      |(fderiv ℝ (restartSectionRadialState h t) Z v).1| ≤ 2 * restartSectionStrongWall h t Z * ‖v‖ := by
    rw [HP.fderiv]
    change |(restartSectionStrongWall h t Z • fderiv ℝ (restartSectionStrongLog h t) Z) v| ≤ _
    rw [← Hn.fderiv]
    exact ((fderiv ℝ (restartSectionStrongWall h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hnD (norm_nonneg _))
  refine ⟨HP.differentiableAt, ?_, hfst⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [Prod.norm_def, max_le_iff]
  constructor
  · exact (hfst v).trans (by nlinarith only [mul_le_mul_of_nonneg_right hn (norm_nonneg v)])
  · rw [HP.fderiv]
    change ‖(restartCompactCenterProjection.comp (fderiv ℝ (restartSectionMixedFlow h t) Z)) v‖ ≤ _
    rw [← HZ.fderiv]
    exact ((fderiv ℝ (restartSectionCenterFlow h t) Z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hZD (norm_nonneg _))

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

private theorem BianchiIX.restartShearDirection_norm {σ : ℝ} (hσ : |σ| = 1) :
    ‖restartShearDirection σ‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i <;> simp [restartShearDirection, hσ]
  · simpa only [restartShearDirection, Matrix.cons_val_zero, Real.norm_eq_abs, hσ] using
      norm_le_pi_norm (restartShearDirection σ) 0

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
open Set

private theorem BianchiIX.restartShearCurve_shear_of_close {a ρ σ n₂ n₃ : ℝ} {W : RestartCenterState}
    (hρ : ρ ∈ Icc a (2 * a)) (hσ : |σ| = 1)
    (hW : ‖W - restartShearCurve σ n₂ n₃ ρ‖ ≤ a / 4) :
    3 * a / 4 ≤ σ * W 0 ∧ σ * W 0 ≤ 9 * a / 4 := by
  have hsq : σ ^ 2 = 1 := by nlinarith only [sq_abs σ, hσ]
  have H := (norm_le_pi_norm (W - restartShearCurve σ n₂ n₃ ρ) 0).trans hW
  change |W 0 - σ * ρ| ≤ a / 4 at H
  have heq : σ * W 0 - ρ = σ * (W 0 - σ * ρ) := by linear_combination ρ * hsq
  have H' : |σ * W 0 - ρ| ≤ a / 4 := by simpa only [heq, abs_mul, hσ, one_mul] using H
  constructor <;> linarith only [(abs_le.mp H').1, (abs_le.mp H').2, hρ.1, hρ.2]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.restartSectionRadialState_center_fderiv {h T : ℝ} {Z : RestartCenterState}
    (H : DifferentiableAt ℝ (restartSectionRadialState h T) Z) (i : Fin 3) (v : RestartCenterState) :
    fderiv ℝ (fun W => restartSectionCenterFlow h T W i) Z v =
      (fderiv ℝ (restartSectionRadialState h T) Z v).2 i := by
  have HD := (ContinuousLinearMap.proj i).hasFDerivAt.comp Z
    ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp Z H.hasFDerivAt)
  change HasFDerivAt (fun W => restartSectionCenterFlow h T W i) _ Z at HD
  rw [HD.fderiv]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearCurve_sharp_control :
    ∃ C ≥ (32 : ℝ), ∀ h a T : ℝ,
      0 < h → C * h ≤ 1 / 4 → (0 < a ∧ a ≤ 1) →
      8 * a ≤ 1 / 16 → 0 ≤ T → C * (8 * a) * T ≤ 1 / 8 →
      ∀ ε σ n₂ n₃ ρ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ρ ∈ Icc a (2 * a) →
          let Z := restartShearCurve σ n₂ n₃ ρ
          let p := restartSectionRadialState h T Z
          let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
          HasDerivAt (fun x => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ x)) v ρ ∧
          normalizedMaxCurve (restartSectionChart h Z) 0 T 0 ≤ -(15 / 16) ∧
          0 < p.1 ∧ p.1 ≤ h * Real.exp (-2 * T) ∧ ‖p.2‖ ≤ 8 * a ∧
          ‖v‖ ≤ 2 ∧ |v.1| ≤ 2 * p.1 ∧
          ∀ i : Fin 2, Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
            |v.2 i.succ| ≤ 8 * C * T * p.2 i.succ := by
  obtain ⟨A, _, HA⟩ := exists_restartSection_fastLayer_control
  obtain ⟨B, _, HB⟩ := exists_restartSectionMixedFlow_derivative
  obtain ⟨D, hD, HD⟩ := exists_restartSectionWeakWall_derivative
  let C := max A (max B D)
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left B D).trans (le_max_right _ _)
  have hDC : D ≤ C := (le_max_right B D).trans (le_max_right _ _)
  have hC : 32 ≤ C := hD.trans hDC
  have hC₀ : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  refine ⟨C, hC, ?_⟩
  intro h a T hh hCh ha hb hT hCb ε σ n₂ n₃ ρ hε hσ h₂ h₃ hρ
  let b := 8 * a
  let Z := restartShearCurve σ n₂ n₃ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
  have hbpos : 0 < b := by dsimp only [b]; positivity [ha.1]
  have hZ := (restartShearCurve_annulus ha.1 hρ hσ hε h₂ h₃).1
  have hZstrict : ‖Z‖ < b / 2 := by dsimp only [b]; linarith only [hZ, ha.1]
  have hbudget (E : ℝ) (hEC : E ≤ C) : E * h ≤ 1 / 4 ∧ E * b * T ≤ 1 / 8 :=
    ⟨(mul_le_mul_of_nonneg_right hEC hh.le).trans hCh,
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEC hbpos.le) hT).trans hCb⟩
  have HF := HA h b T Z hh (hbudget A hAC).1 ⟨hbpos, hb⟩ hT (hbudget A hAC).2 hZstrict.le T ⟨hT, le_rfl⟩
  have HM := (HB h b T hh (hbudget B hBC).1 ⟨hbpos, hb⟩ hT (hbudget B hBC).2 T ⟨hT, le_rfl⟩).1 Z hZstrict.le
  have HW (i : Fin 2) := HD h b T hh (hbudget D hDC).1 ⟨hbpos, hb⟩ hT (hbudget D hDC).2 Z hZstrict i
  have hhsmall : h ≤ 1 / 16 := by nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh]) (by linarith only [hZstrict.le, hb])
  have hn : restartSectionStrongWall h T Z ≤ 1 := by
    have Hexp : Real.exp (-2 * T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hT])
    change normalizedMaxCurve (restartSectionChart h Z) 0 T 2 ≤ 1
    exact HF.2.1.trans ((mul_le_mul_of_nonneg_left Hexp hh.le).trans (by linarith only [hhsmall]))
  have HS := restartSectionRadialState_derivative hh hrad hT HM.1 (HM.2.trans exp_one_quarter_lt_two.le) hn
  have Hcurve := HS.1.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_restartShearCurve σ n₂ n₃ ρ)
  have hvnorm : ‖v‖ ≤ 2 := by
    have H := (fderiv ℝ (restartSectionRadialState h T) Z).le_opNorm (restartShearDirection σ)
    rw [restartShearDirection_norm hσ, mul_one] at H
    exact H.trans HS.2.1
  have hnpos : 0 < p.1 := HF.1
  refine ⟨Hcurve, HF.2.2.1, hnpos, HF.2.1, HF.2.2.2.2.le, hvnorm, ?_, ?_⟩
  · have H := HS.2.2 (restartShearDirection σ)
    rw [restartShearDirection_norm hσ, mul_one] at H
    exact H
  · intro i
    have hZi : 0 ≤ Z i.succ := by fin_cases i; exact h₂.1; exact h₃.1
    have hformula : p.2 i.succ = Z i.succ * restartSectionWeakMultiplier h T i Z := (HW i).1
    have hpi : 0 ≤ p.2 i.succ := by
      rw [hformula]
      exact mul_nonneg hZi (by linarith only [(HW i).2.1.1])
    change Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
      |v.2 i.succ| ≤ 8 * C * T * p.2 i.succ
    refine ⟨?_, ?_, ?_⟩
    · rw [hformula]
      nlinarith only [mul_le_mul_of_nonneg_left (HW i).2.1.1.le hZi]
    · rw [hformula]
      nlinarith only [mul_le_mul_of_nonneg_left (HW i).2.1.2.le hZi]
    · have H := (HW i).2.2.2 (restartShearDirection σ) (by fin_cases i <;> rfl)
      rw [restartSectionRadialState_center_fderiv HS.1, restartShearDirection_norm hσ, mul_one] at H
      change |v.2 i.succ| ≤ 8 * D * T * |p.2 i.succ| at H
      rw [abs_of_nonneg hpi] at H
      exact H.trans (by gcongr)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearCurve_control :
    ∃ C ≥ (32 : ℝ), ∀ h a T : ℝ,
      0 < h → C * h ≤ 1 / 4 → (0 < a ∧ a ≤ 1) →
      8 * a ≤ 1 / 16 → 0 ≤ T → C * (8 * a) * T ≤ 1 / 8 → a * T ≤ 1 →
      ∀ ε σ n₂ n₃ ρ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ρ ∈ Icc a (2 * a) →
          let Z := restartShearCurve σ n₂ n₃ ρ
          let p := restartSectionRadialState h T Z
          let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
          HasDerivAt (fun x => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ x)) v ρ ∧
          normalizedMaxCurve (restartSectionChart h Z) 0 T 0 ≤ -(15 / 16) ∧
          0 < p.1 ∧ p.1 ≤ h * Real.exp (-2 * T) ∧ ‖p.2‖ ≤ 8 * a ∧
          ‖v‖ ≤ 2 ∧ |v.1| ≤ 2 * p.1 / a ∧
          ∀ i : Fin 2, Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
            |v.2 i.succ| ≤ 8 * C * p.2 i.succ / a := by
  obtain ⟨C, hC, HC⟩ := exists_restartShearCurve_sharp_control
  refine ⟨C, hC, ?_⟩
  intro h a T hh hCh ha hb hT hCb haT ε σ n₂ n₃ ρ hε hσ h₂ h₃ hρ Z p v
  obtain ⟨Hcurve, hp, hn, hne, hcenter, hv, hnv, HW⟩ :=
    HC h a T hh hCh ha hb hT hCb ε σ n₂ n₃ ρ hε hσ h₂ h₃ hρ
  refine ⟨Hcurve, hp, hn, hne, hcenter, hv, ?_, ?_⟩
  · apply (le_div_iff₀ ha.1).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hnv ha.1.le,
      mul_le_mul_of_nonneg_left ha.2 hn.le]
  · intro i
    have hZi : 0 ≤ Z i.succ := by fin_cases i; exact h₂.1; exact h₃.1
    have hpi : 0 ≤ p.2 i.succ := (div_nonneg hZi (by norm_num)).trans (HW i).1
    refine ⟨(HW i).1, (HW i).2.1, (le_div_iff₀ ha.1).mpr ?_⟩
    have HT := mul_le_mul_of_nonneg_left haT
      (show 0 ≤ 8 * C * p.2 i.succ by positivity [le_trans (by norm_num : (0 : ℝ) ≤ 32) hC])
    nlinarith only [mul_le_mul_of_nonneg_right (HW i).2.2 ha.1.le, HT]

end
end

/-- Both signed shear families reach the fast-layer endpoint with preserved shear and wall-relative derivatives. -/
theorem solution :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q : ℝ, 2 < q → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε σ n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let Z := restartShearCurve σ n₂ n₃ ρ
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
            let p := restartSectionRadialState h T Z
            let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
            a ≤ 1 ∧ 8 * a ≤ 1 / 16 ∧ 0 ≤ T ∧ 0 < restartSectionRadicand h Z ∧
            T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧ stateConstraint x = 1 ∧ x 0 ≤ -(15 / 16) ∧
            HasDerivAt (fun y => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ y)) v ρ ∧
            0 < p.1 ∧ p.1 ≤ h * a ^ q ∧
            (3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4) ∧ ‖p.2‖ ≤ 8 * a ∧
            ‖v‖ ≤ 2 ∧ |v.1| ≤ 2 * p.1 / a ∧
            ∀ i : Fin 2, Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
              |v.2 i.succ| ≤ 8 * C * p.2 i.succ / a := by
  obtain ⟨C, hC, HC⟩ := exists_restartShearCurve_control
  obtain ⟨hL, hhL, HL⟩ := exists_restartSection_linear_approximation
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨C, hC, min hL (min (1 / (4 * C)) (1 / 64)),
    lt_min hhL (lt_min (by positivity) (by norm_num)), ?_⟩
  intro h hh q hq
  have hhsmall : h ≤ 1 / 64 := hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp
      (hh.2.trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [H]
  obtain ⟨K, _, aL, haL, HLa⟩ := HL h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ 2 (by norm_num) q hq
  have HI : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have Hlog : Tendsto (fun a : ℝ => a * Real.log a) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HE : Tendsto (fun a : ℝ => K * (a + |a * Real.log a|)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [abs_zero, add_zero, mul_zero] using (HI.add Hlog.abs).const_mul K
  have Hbudget : ∀ᶠ a : ℝ in 𝓝[>] 0,
      ((0 < a ∧ a ≤ 1) ∧ 8 * a ≤ 1 / 16 ∧ C * (8 * a) * (q / 2 * Real.log (1 / a)) ≤ 1 / 8) ∧
      a * (q / 2 * Real.log (1 / a)) ≤ 1 ∧ K * (a + |a * Real.log a|) ≤ 1 / 8 := by
    filter_upwards [eventually_restart_cutoff_budget C 4 q, eventually_restart_cutoff_budget 1 1 q,
      HE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with a H₁ H₂ H₃
    exact ⟨by simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using H₁,
      by nlinarith only [H₂.2.2], H₃.le⟩
  obtain ⟨aB, haB, HBa⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hbudget
  refine ⟨min aL aB, lt_min haL haB, ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T Z x p v
  have Ha := HBa ⟨ha.1, ha.2.trans (min_le_right _ _)⟩
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq] : 0 ≤ q / 2)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by linarith only [Ha.1.1.2])))
  obtain ⟨Hcurve, hneg, hnpos, hnexp, hcenter, hv, hnv, hwv⟩ := HC h a T hh.1 hCh Ha.1.1
    Ha.1.2.1 hT Ha.1.2.2 Ha.2.1 ε σ n₂ n₃ ρ hε hσ h₂ h₃ hρ
  have hZ := (restartShearCurve_annulus ha.1 hρ hσ hε h₂ h₃).1
  have hlin := HLa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ Z hZ
  have herror : ‖restartSectionRemainder h T Z‖ ≤ a / 8 := by
    apply hlin.2.2.2.2.2.1.trans
    have H := mul_le_mul_of_nonneg_left Ha.2.2 ha.1.le
    rw [abs_mul, abs_of_pos ha.1] at H
    nlinarith only [H]
  have htransfer : ‖restartCenterTransfer h Z - Z‖ ≤ a / 8 := by
    have H := (restartCenterTransfer h - ContinuousLinearMap.id ℝ RestartCenterState).le_opNorm Z
    change ‖restartCenterTransfer h Z - Z‖ ≤ _ at H
    have HCbound := restartCenterTransfer_sub_id_bound ⟨hh.1.le, by linarith only [hhsmall]⟩
    have H' := H.trans (mul_le_mul HCbound hZ (norm_nonneg Z) (by positivity [hh.1]))
    exact H'.trans (by nlinarith only [mul_le_mul_of_nonneg_right hhsmall ha.1.le, ha.1])
  have hclose : ‖restartSectionCenterFlow h T Z - Z‖ ≤ a / 4 := by
    rw [hlin.2.2.2.1]
    have heq : restartCenterTransfer h Z + restartSectionRemainder h T Z - Z =
        (restartCenterTransfer h Z - Z) + restartSectionRemainder h T Z := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith only [htransfer, herror])
  have hshear := restartShearCurve_shear_of_close hρ hσ hclose
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rw [abs_of_pos hh.1]; linarith only [hhsmall]) (by linarith only [hZ, Ha.1.2.1])
  have he : Real.exp (-2 * T) = a ^ q := by
    rw [Real.rpow_def_of_pos ha.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  rw [he] at hnexp
  exact ⟨Ha.1.1.2, Ha.1.2.1, hT, hrad, hlin.1,
    (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hrad.le) hT).2.1,
    hneg, Hcurve, hnpos, hnexp, hshear, hcenter, hv, hnv, hwv⟩
