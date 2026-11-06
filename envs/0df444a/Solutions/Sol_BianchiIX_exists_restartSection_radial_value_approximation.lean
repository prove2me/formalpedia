-- Prove2me | solution 1 for BianchiIX.exists_restartSection_radial_value_approximation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:40:16.599984+00:00
-- url     : https://prove2.me/submissions/83bb06a6-350d-4e88-8230-c162d8fbc916

import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Theorems.Thm_BianchiIX_exists_bounds_of_vanishing_axis
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity

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

private theorem BianchiIX.abs_sqrt_sub_sqrt_le_of_relative_error {a b A : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (H : |a - b| ≤ A * b) : |Real.sqrt a - Real.sqrt b| ≤ A * Real.sqrt b := by
  by_cases hb0 : b = 0
  · have Ha : a ≤ 0 := by simpa [hb0, abs_of_nonneg ha] using H
    have ha0 : a = 0 := le_antisymm Ha ha
    simp [ha0, hb0]
  have hbpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr (lt_of_le_of_ne hb (Ne.symm hb0))
  have heq : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a - b| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)), ← abs_mul]
    congr 1
    nlinarith only [Real.sq_sqrt ha, Real.sq_sqrt hb]
  have HB : |Real.sqrt a - Real.sqrt b| * Real.sqrt b ≤ (A * Real.sqrt b) * Real.sqrt b := by
    calc
      _ ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg a)) (abs_nonneg _)
      _ ≤ A * b := heq.le.trans H
      _ = A * (Real.sqrt b) ^ 2 := congrArg (fun x => A * x) (Real.sq_sqrt hb).symm
      _ = _ := by ring
  exact (mul_le_mul_iff_of_pos_right hbpos).mp HB

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartReferenceRoot_pos {n : ℝ} (hn : n ^ 2 < 1) : 0 < restartReferenceRoot n :=
  Real.sqrt_pos.mpr (sub_pos.mpr hn)

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

private theorem BianchiIX.hasDerivAt_restartReferenceRoot {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartReferenceRoot (-n / restartReferenceRoot n) n := by
  convert! (((hasDerivAt_id' n).pow 2).const_sub 1).sqrt (sub_pos.mpr hn).ne' using 1
  simp only [Pi.pow_apply]
  dsimp only [restartReferenceRoot]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartShearFactor {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartShearFactor
      (3 * n / (restartReferenceRoot n * (2 + restartReferenceRoot n) ^ 2)) n := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  convert! (hasDerivAt_const n (3 : ℝ)).div
    ((hasDerivAt_restartReferenceRoot hn).const_add 2) hd using 1
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartWallFactor {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartWallFactor (9 * n / (2 * (2 + restartReferenceRoot n) ^ 3)) n := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  have hroot := hasDerivAt_restartReferenceRoot hn
  convert! ((hroot.const_add 1).const_mul 9).div
    (((hroot.const_add 2).pow 2).const_mul 2)
    (by change 2 * (2 + restartReferenceRoot n) ^ 2 ≠ 0; positivity) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartShearCoupling {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartShearCoupling
      (3 * Real.sqrt 3 * (restartReferenceRoot n * (2 + restartReferenceRoot n) + 2 * n ^ 2) /
        (restartReferenceRoot n * (2 + restartReferenceRoot n) ^ 3)) n := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  convert! ((hasDerivAt_id' n).const_mul (3 * Real.sqrt 3)).div
    (((hasDerivAt_restartReferenceRoot hn).const_add 2).pow 2) (pow_ne_zero 2 hd) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restart_transport_cancellation {n : ℝ} (hn : n ^ 2 < 1) :
    n * restartReferenceStrongRate n * deriv restartShearFactor n + restartShearFactor n * n ^ 2 = 0 ∧
    n * restartReferenceStrongRate n * deriv restartWallFactor n +
      restartWallFactor n * restartReferenceWallRate n = 0 ∧
    n * restartReferenceStrongRate n * deriv restartShearCoupling n +
      restartShearFactor n * Real.sqrt 3 * n +
      restartShearCoupling n * restartReferenceWallRate n = 0 := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  have hn2 : n ^ 2 = 1 - restartReferenceRoot n ^ 2 := by
    linarith only [restartReferenceRoot_sq hn.le]
  have hF : restartReferenceStrongRate n = -restartReferenceRoot n * (2 + restartReferenceRoot n) := by
    dsimp only [restartReferenceStrongRate]
    rw [hn2]
    ring
  have hb : restartReferenceWallRate n = restartReferenceRoot n * (1 - restartReferenceRoot n) := by
    dsimp only [restartReferenceWallRate]
    rw [hn2]
    ring
  rw [(hasDerivAt_restartShearFactor hn).deriv, (hasDerivAt_restartWallFactor hn).deriv,
    (hasDerivAt_restartShearCoupling hn).deriv, hF, hb]
  dsimp only [restartShearFactor, restartWallFactor, restartShearCoupling]
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    linear_combination -9 * restartReferenceRoot n * (restartReferenceRoot_sq hn.le)
  · field_simp
    linear_combination -6 * Real.sqrt 3 * n * (restartReferenceRoot_sq hn.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restart_coefficients_zero :
    restartShearFactor 0 = 1 ∧ restartWallFactor 0 = 1 ∧ restartShearCoupling 0 = 0 := by
  norm_num [restartShearFactor, restartWallFactor, restartShearCoupling, restartReferenceRoot]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restart_coefficients {n : ℝ} (hn : n ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartShearFactor n ∧ ContDiffAt ℝ k restartWallFactor n ∧
      ContDiffAt ℝ k restartShearCoupling n := by
  have hr : ContDiffAt ℝ k restartReferenceRoot n :=
    (contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt (sub_pos.mpr hn).ne'
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity [restartReferenceRoot_pos hn]
  refine ⟨contDiffAt_const.div (contDiffAt_const.add hr) hd, ?_, ?_⟩
  · exact (contDiffAt_const.mul (contDiffAt_const.add hr)).div
      (contDiffAt_const.mul ((contDiffAt_const.add hr).pow 2)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd))
  · exact (contDiffAt_const.mul contDiffAt_id).div ((contDiffAt_const.add hr).pow 2) (pow_ne_zero 2 hd)

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

private theorem BianchiIX.curvature_restart_decomposition (x : NormalizedState) :
    curvature (x 2) (x 3) (x 4) = x 2 ^ 2 + restartCurvatureDifference x := by
  dsimp only [curvature, restartCurvatureDifference]
  ring

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

private theorem BianchiIX.hasDerivAt_restart_components {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1) :
    HasDerivAt (fun r => x r 2)
      (x t 2 * (restartReferenceStrongRate (x t 2) + restartStrongRateDifference (x t))) t ∧
    HasDerivAt (fun r => x r 1)
      (x t 2 ^ 2 * x t 1 + Real.sqrt 3 * x t 2 * (x t 3 - x t 4) +
        (restartCurvatureDifference (x t) * x t 1 - Real.sqrt 3 * (x t 3 + x t 4) * (x t 3 - x t 4))) t ∧
    HasDerivAt (fun r => x r 3 - x r 4)
      (restartReferenceWallRate (x t 2) * (x t 3 - x t 4) +
        (restartCurvatureDifference (x t) + restartRootDifference (x t)) * (x t 3 - x t 4) +
        Real.sqrt 3 * (x t 3 + x t 4) * x t 1) t := by
  obtain ⟨_, hs, hn, ha, hb⟩ := hasDerivAt_normalized_components hx
  have hq : shearSq (x t 0) (x t 1) = 1 - curvature (x t 2) (x t 3) (x t 4) := by
    dsimp only [stateConstraint, constraint] at hc
    linarith only [hc]
  refine ⟨hn.congr_deriv ?_, hs.congr_deriv ?_, (ha.sub hb).congr_deriv ?_⟩
  · dsimp only [rateOne, restartReferenceStrongRate, restartStrongRateDifference, restartRootDifference]
    rw [hq, curvature_restart_decomposition]
    ring
  · dsimp only [shearMinus, curvature, restartCurvatureDifference]
    ring
  · dsimp only [rateTwo, rateThree, restartReferenceWallRate, restartRootDifference]
    rw [hq, curvature_restart_decomposition]
    ring

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

private theorem BianchiIX.abs_quadraticFromCoefficients_le_radius {r s v : ℝ} (m : Fin 3 → ℝ)
    (_hr : 0 ≤ r) (hs : |s| ≤ r) (hv : |v| ≤ 2 * r) :
    |quadraticFromCoefficients m s v| ≤ 12 * ‖m‖ * r ^ 2 := by
  have hs2 : s ^ 2 ≤ r ^ 2 := by
    have H := mul_self_le_mul_self (abs_nonneg s) hs
    nlinarith only [H, sq_abs s]
  have hv2 : v ^ 2 ≤ 4 * r ^ 2 := by
    have H := mul_self_le_mul_self (abs_nonneg v) hv
    nlinarith only [H, sq_abs v]
  exact (abs_quadraticFromCoefficients_le m s v).trans (by
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hs2 hv2) (norm_nonneg m),
      mul_nonneg (norm_nonneg m) (sq_nonneg r)])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.abs_quadratic_tangent_le {r d s v ds dv : ℝ} (m dm : Fin 3 → ℝ)
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hs : |s| ≤ r) (hv : |v| ≤ 2 * r)
    (hds : |ds| ≤ d) (hdv : |dv| ≤ 2 * d) :
    |quadraticFromCoefficients dm s v + (2 * m 0 * s + m 1 * v) * ds +
      (m 1 * s + 2 * m 2 * v) * dv| ≤ 12 * ‖dm‖ * r ^ 2 + 24 * ‖m‖ * r * d := by
  have hm (i : Fin 3) : |m i| ≤ ‖m‖ := norm_le_pi_norm m i
  have Hs : |(2 * m 0 * s + m 1 * v) * ds| ≤ 4 * ‖m‖ * r * d := by
    calc
      _ ≤ (|2 * m 0 * s| + |m 1 * v|) * |ds| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
      _ ≤ (2 * ‖m‖ * r + ‖m‖ * (2 * r)) * d := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
        · exact hm 0
        · exact hm 1
      _ = _ := by ring
  have Hv : |(m 1 * s + 2 * m 2 * v) * dv| ≤ 10 * ‖m‖ * r * d := by
    calc
      _ ≤ (|m 1 * s| + |2 * m 2 * v|) * |dv| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
      _ ≤ (‖m‖ * r + 2 * ‖m‖ * (2 * r)) * (2 * d) := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
        · exact hm 1
        · exact hm 2
      _ = _ := by ring
  have H : |quadraticFromCoefficients dm s v + (2 * m 0 * s + m 1 * v) * ds +
      (m 1 * s + 2 * m 2 * v) * dv| ≤ |quadraticFromCoefficients dm s v| +
        |(2 * m 0 * s + m 1 * v) * ds| + |(m 1 * s + 2 * m 2 * v) * dv| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have HQ := abs_quadraticFromCoefficients_le_radius dm hr hs hv
  nlinarith only [H, HQ, Hs, Hv, mul_nonneg (mul_nonneg (norm_nonneg m) hr) hd]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartQuadratic_coercive {n : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16) (s v : ℝ) :
    s ^ 2 + v ^ 2 ≤ 2 * restartQuadratic n s v := by
  obtain ⟨ha0, _, hc0, _, hk0, hk1⟩ := restart_coefficients_small hn
  have ha2 : 1 ≤ restartShearFactor n ^ 2 := by nlinarith only [ha0]
  have hc2 : 1 ≤ restartWallFactor n ^ 2 := by nlinarith only [hc0]
  have hk2 : 2 * restartShearCoupling n ^ 2 ≤ 1 := by nlinarith only [hk0, hk1, hn.2]
  have HA := mul_le_mul_of_nonneg_right ha2 (sq_nonneg s)
  have HC := mul_le_mul_of_nonneg_right hc2 (sq_nonneg v)
  have HK := mul_le_mul_of_nonneg_right hk2 (sq_nonneg v)
  dsimp only [restartQuadratic]
  nlinarith only [HA, HC, HK, sq_nonneg (restartShearFactor n * s + 2 * restartShearCoupling n * v)]

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

private theorem BianchiIX.hasDerivAt_restart_transported_components
    {n s v : ℝ → ℝ} {t dF es ev : ℝ} (hn₀ : n t ^ 2 < 1)
    (hn : HasDerivAt n (n t * (restartReferenceStrongRate (n t) + dF)) t)
    (hs : HasDerivAt s (n t ^ 2 * s t + Real.sqrt 3 * n t * v t + es) t)
    (hv : HasDerivAt v (restartReferenceWallRate (n t) * v t + ev) t) :
    HasDerivAt (fun r => restartShearFactor (n r) * s r + restartShearCoupling (n r) * v r)
      (n t * dF * (deriv restartShearFactor (n t) * s t + deriv restartShearCoupling (n t) * v t) +
        restartShearFactor (n t) * es + restartShearCoupling (n t) * ev) t ∧
    HasDerivAt (fun r => restartWallFactor (n r) * v r)
      (n t * dF * deriv restartWallFactor (n t) * v t + restartWallFactor (n t) * ev) t := by
  have HA := (hasDerivAt_restartShearFactor hn₀).differentiableAt.hasDerivAt.comp t hn
  have HC := (hasDerivAt_restartWallFactor hn₀).differentiableAt.hasDerivAt.comp t hn
  have HK := (hasDerivAt_restartShearCoupling hn₀).differentiableAt.hasDerivAt.comp t hn
  obtain ⟨ha, hc, hk⟩ := restart_transport_cancellation hn₀
  constructor
  · convert! (HA.mul hs).add (HK.mul hv) using 1
    simp only [Function.comp_def]
    linear_combination -(s t) * ha - (v t) * hk
  · convert! HC.mul hv using 1
    simp only [Function.comp_def]
    linear_combination -(v t) * hc

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartQuadratic_perturbed
    {n s v : ℝ → ℝ} {t dF es ev : ℝ} (hn₀ : n t ^ 2 < 1)
    (hn : HasDerivAt n (n t * (restartReferenceStrongRate (n t) + dF)) t)
    (hs : HasDerivAt s (n t ^ 2 * s t + Real.sqrt 3 * n t * v t + es) t)
    (hv : HasDerivAt v (restartReferenceWallRate (n t) * v t + ev) t) :
    HasDerivAt (fun r => restartQuadratic (n r) (s r) (v r))
      (n t * dF * restartQuadraticStrongDerivative (n t) (s t) (v t) +
        2 * (restartShearFactor (n t) * s t + restartShearCoupling (n t) * v t) *
          (restartShearFactor (n t) * es + restartShearCoupling (n t) * ev) +
        2 * restartWallFactor (n t) ^ 2 * v t * ev) t := by
  obtain ⟨HS, HV⟩ := hasDerivAt_restart_transported_components hn₀ hn hs hv
  convert! (HS.pow 2).add (HV.pow 2) using 1
  dsimp only [restartQuadraticStrongDerivative]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartQuadratic_normalized {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1)
    (hn : x t 2 ^ 2 < 1) :
    HasDerivAt (fun r => restartQuadratic (x r 2) (x r 1) (x r 3 - x r 4))
      (x t 2 * restartStrongRateDifference (x t) *
          restartQuadraticStrongDerivative (x t 2) (x t 1) (x t 3 - x t 4) +
        2 * restartCurvatureDifference (x t) * restartQuadratic (x t 2) (x t 1) (x t 3 - x t 4) +
        2 * restartRootDifference (x t) * (x t 3 - x t 4) *
          (restartShearFactor (x t 2) * restartShearCoupling (x t 2) * x t 1 +
            (restartShearCoupling (x t 2) ^ 2 + restartWallFactor (x t 2) ^ 2) * (x t 3 - x t 4)) +
        2 * Real.sqrt 3 * (x t 3 + x t 4) * restartRotationDefect (x t 2) (x t 1) (x t 3 - x t 4)) t := by
  obtain ⟨HN, HS, HV⟩ := hasDerivAt_restart_components hx hc
  have HV' : HasDerivAt (fun r => x r 3 - x r 4)
      (restartReferenceWallRate (x t 2) * (x t 3 - x t 4) +
        ((restartCurvatureDifference (x t) + restartRootDifference (x t)) * (x t 3 - x t 4) +
          Real.sqrt 3 * (x t 3 + x t 4) * x t 1)) t := by
    convert! HV using 1
    ring
  convert! hasDerivAt_restartQuadratic_perturbed hn HN HS HV' using 1
  dsimp only [restartQuadratic, restartRotationDefect]
  ring

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

private theorem BianchiIX.sqrt_restartQuadratic_tail {n r s v : ℝ} (hn : 0 ≤ n ∧ n ≤ 1 / 16)
    (hr : 0 ≤ r) (hs : |s| ≤ r) (hv : |v| ≤ 2 * r) :
    |Real.sqrt (restartQuadratic n s v) - Real.sqrt (s ^ 2 + v ^ 2)| ≤ 24 * n * r := by
  have HJ : 0 ≤ restartQuadratic n s v := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have HY : 0 ≤ s ^ 2 + v ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have H := abs_sqrt_sub_sqrt_le_of_relative_error HJ HY (restartQuadratic_relative_error hn s v)
  have hs2 := mul_self_le_mul_self (abs_nonneg s) hs
  have hv2 := mul_self_le_mul_self (abs_nonneg v) hv
  have Hnorm : Real.sqrt (s ^ 2 + v ^ 2) ≤ 3 * r := by
    nlinarith only [Real.sq_sqrt HY, Real.sqrt_nonneg (s ^ 2 + v ^ 2), hs2, hv2, sq_abs s, sq_abs v, hr]
  exact H.trans (by nlinarith only [mul_le_mul_of_nonneg_left Hnorm hn.1])

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
open Set

private theorem BianchiIX.scalar_clock_comparison {f f' z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ z' t * f t) :
    ∀ t ∈ Icc a b,
      f a * Real.exp (-(z t - z a)) ≤ f t ∧ f t ≤ f a * Real.exp (z t - z a) := by
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have HU := le_exp_of_clock_deriv_le (convex_Icc a b) hf hz (c := 1)
    (fun s hs => by simpa only [one_mul] using (le_abs_self _).trans (hb s hs)) ha ht ht.1
  have HL := le_exp_of_clock_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).neg) hz (c := -1)
    (fun s hs => by
      change -f' s ≤ -1 * z' s * (-f s)
      nlinarith only [neg_le_abs (f' s), hb s hs]) ha ht ht.1
  simp only [one_mul] at HU
  simp only [Pi.neg_apply, neg_one_mul] at HL
  exact ⟨by linarith only [HL], HU⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.abs_sub_le_of_deriv_primitive {f f' z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ z' t) :
    ∀ t ∈ Icc a b, |f t - f a| ≤ z t - z a := by
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have HU := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [le_abs_self (f' s), hb s hs]) ha ht ht.1
  have HL := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).neg.sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [neg_le_abs (f' s), hb s hs]) ha ht ht.1
  simp only [zero_mul, Real.exp_zero, mul_one, Pi.sub_apply, Pi.neg_apply] at HU HL
  exact abs_le.mpr ⟨by linarith only [HL], by linarith only [HU]⟩

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

private theorem BianchiIX.contDiffAt_restartGramCoefficients {n : ℝ} (hn : n ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartGramCoefficients n ∧
      ContDiffAt ℝ k restartRootCoefficients n ∧ ContDiffAt ℝ k restartRotationCoefficients n := by
  obtain ⟨ha, hc, hk⟩ := contDiffAt_restart_coefficients hn k
  constructor
  · rw [contDiffAt_pi]
    intro i
    fin_cases i <;> dsimp [restartGramCoefficients] <;> fun_prop
  constructor <;> rw [contDiffAt_pi] <;> intro i <;>
    fin_cases i <;> dsimp [restartRootCoefficients, restartRotationCoefficients] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.deriv_restartGramCoefficients {n : ℝ} (hn : n ^ 2 < 1) :
    deriv restartGramCoefficients n =
      ![2 * restartShearFactor n * deriv restartShearFactor n,
        2 * (deriv restartShearFactor n * restartShearCoupling n +
          restartShearFactor n * deriv restartShearCoupling n),
        2 * (restartShearCoupling n * deriv restartShearCoupling n +
          restartWallFactor n * deriv restartWallFactor n)] := by
  have ha := (hasDerivAt_restartShearFactor hn).differentiableAt.hasDerivAt
  have hc := (hasDerivAt_restartWallFactor hn).differentiableAt.hasDerivAt
  have hk := (hasDerivAt_restartShearCoupling hn).differentiableAt.hasDerivAt
  apply HasDerivAt.deriv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun m => restartShearFactor m ^ 2)
      (2 * restartShearFactor n * deriv restartShearFactor n) n
    convert! ha.pow 2 using 1
    ring
  · change HasDerivAt (fun m => 2 * restartShearFactor m * restartShearCoupling m)
      (2 * (deriv restartShearFactor n * restartShearCoupling n +
        restartShearFactor n * deriv restartShearCoupling n)) n
    convert! (ha.const_mul 2).mul hk using 1
    ring
  · change HasDerivAt (fun m => restartShearCoupling m ^ 2 + restartWallFactor m ^ 2)
      (2 * (restartShearCoupling n * deriv restartShearCoupling n +
        restartWallFactor n * deriv restartWallFactor n)) n
    convert! (hk.pow 2).add (hc.pow 2) using 1
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartRadialDriftCoefficients_axis (n : ℝ) : restartRadialDriftCoefficients (n, 0) = 0 := by
  simp [restartRadialDriftCoefficients, restartRadialCurvatureDifference, restartRadialRootDifference,
    restartSectionRadicand, curvature, restartReferenceRoot]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartRotationCoefficients_zero : restartRotationCoefficients 0 = 0 := by
  ext i
  fin_cases i <;> simp [restartRotationCoefficients, restart_coefficients_zero.1,
    restart_coefficients_zero.2.1, restart_coefficients_zero.2.2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartRadialDriftCoefficients {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) :
    ContDiffAt ℝ 3 restartRadialDriftCoefficients p := by
  have hQ : ContDiff ℝ 3 restartRadialCurvatureDifference := by
    unfold restartRadialCurvatureDifference
    fun_prop
  have hrad : ContDiff ℝ 3 (fun p : RestartRadialState => restartSectionRadicand p.1 p.2) := by
    unfold restartSectionRadicand curvature
    fun_prop
  have hroot : ContDiffAt ℝ 3 (fun p : RestartRadialState => restartReferenceRoot p.1) p :=
    (contDiffAt_const.sub (contDiffAt_fst.pow 2)).sqrt (sub_pos.mpr hn).ne'
  have hdiff : ContDiffAt ℝ 3 restartRadialRootDifference p := (hrad.contDiffAt.sqrt hr.ne').sub hroot
  have hG := (contDiffAt_restartGramCoefficients hn 3).1.comp p contDiffAt_fst
  have hH := (contDiffAt_restartGramCoefficients hn 3).2.1.comp p contDiffAt_fst
  have hR := (contDiffAt_restartGramCoefficients hn 3).2.2.comp p contDiffAt_fst
  have hG' := (((contDiffAt_restartGramCoefficients hn 4).1).derivWithin
    (by norm_num : (3 : WithTop ℕ∞) + 1 ≤ 4)).comp p contDiffAt_fst
  unfold restartRadialDriftCoefficients
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasFDerivAt_restartRadialDifferences_zero :
    HasFDerivAt (𝕜 := ℝ) restartRadialCurvatureDifference 0 0 ∧
      HasFDerivAt (𝕜 := ℝ) restartRadialRootDifference 0 0 := by
  have hn : DifferentiableAt ℝ (fun p : RestartRadialState => p.1) 0 := by fun_prop
  have hp (i : Fin 3) : DifferentiableAt ℝ (fun p : RestartRadialState => p.2 i) 0 := by fun_prop
  have hQ : HasFDerivAt (𝕜 := ℝ) restartRadialCurvatureDifference 0 0 := by
    convert! (((hp 1).hasFDerivAt.sub (hp 2).hasFDerivAt).pow 2).sub
      ((hn.hasFDerivAt.mul ((hp 1).hasFDerivAt.add (hp 2).hasFDerivAt)).const_mul 2) using 1
    · ext p
      dsimp [restartRadialCurvatureDifference]
      ring
    · simp
  have hrad : HasFDerivAt (𝕜 := ℝ)
      (fun p : RestartRadialState => restartSectionRadicand p.1 p.2) 0 0 := by
    have H := (((hp 0).hasFDerivAt.pow 2).const_sub 1).sub ((hn.hasFDerivAt.pow 2).add hQ)
    convert! H using 1
    · ext p
      dsimp [restartSectionRadicand, restartRadialCurvatureDifference, curvature]
      ring
    · simp
  have hroot0 : HasFDerivAt (𝕜 := ℝ) (fun p : RestartRadialState => restartReferenceRoot p.1) 0 0 := by
    convert! ((hn.hasFDerivAt.pow 2).const_sub 1).sqrt (by norm_num : (1 : ℝ) - (0 : ℝ) ^ 2 ≠ 0) using 1
    simp
  refine ⟨hQ, ?_⟩
  convert! (hrad.sqrt (by norm_num [restartSectionRadicand, curvature])).sub hroot0 using 1
  simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartRadialDriftCoefficients_fderiv_zero : fderiv ℝ restartRadialDriftCoefficients 0 = 0 := by
  obtain ⟨hQ, hξ⟩ := hasFDerivAt_restartRadialDifferences_zero
  have hn : HasFDerivAt (fun p : RestartRadialState => p.1) (ContinuousLinearMap.fst ℝ ℝ RestartCenterState) 0 :=
    hasFDerivAt_fst
  have hp (i : Fin 3) : DifferentiableAt ℝ (fun p : RestartRadialState => p.2 i) 0 := by fun_prop
  have hg := contDiffAt_restartGramCoefficients (by norm_num : (0 : ℝ) ^ 2 < 1) 2
  have hG := (hg.1.comp (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have hH := (hg.2.1.comp (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have hR := (hg.2.2.comp (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have hG' := ((hg.1.derivWithin (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).comp
    (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have H := (((hn.mul (hQ.sub (hξ.const_mul 2))).smul hG'.hasFDerivAt).add
    ((hQ.const_mul 2).smul hG.hasFDerivAt) |>.add
    ((hξ.const_mul 2).smul hH.hasFDerivAt)).add
    ((((hp 1).hasFDerivAt.add (hp 2).hasFDerivAt).const_mul (2 * Real.sqrt 3)).smul hR.hasFDerivAt)
  have HD : HasFDerivAt (𝕜 := ℝ) restartRadialDriftCoefficients 0 0 := by
    convert! H using 1
    simp [restartRadialCurvatureDifference, restartRadialRootDifference, restartSectionRadicand,
      curvature, restartReferenceRoot, restartRotationCoefficients_zero]
  exact HD.fderiv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartRadialDriftCoefficients_bounds :
    ∃ C ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState), |n| ≤ 1 / 16 → ‖Z‖ ≤ 1 / 16 →
      ‖restartRadialDriftCoefficients (n, Z)‖ ≤ C * (|n| + ‖Z‖) * ‖Z‖ ∧
      ‖fderiv ℝ restartRadialDriftCoefficients (n, Z)‖ ≤ C * (|n| + ‖Z‖) ∧
      ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (1, 0)‖ ≤ C * ‖Z‖ := by
  have hreg (p : RestartRadialState) (hp : ‖p‖ ≤ 1 / 16) :
      ContDiffAt ℝ 3 restartRadialDriftCoefficients p := by
    have hn : |p.1| ≤ 1 / 16 := (norm_fst_le p).trans hp
    have hZ := (norm_snd_le p).trans hp
    exact contDiffAt_restartRadialDriftCoefficients
      (by obtain ⟨hl, hu⟩ := abs_le.mp hn; nlinarith only [hl, hu])
      (restartSectionRadicand_pos_of_small hn hZ)
  obtain ⟨C, hC, HC⟩ := exists_bounds_of_vanishing_axis (by norm_num : (0 : ℝ) ≤ 1 / 16)
    hreg restartRadialDriftCoefficients_axis restartRadialDriftCoefficients_fderiv_zero
  refine ⟨C, hC, ?_⟩
  intro n Z hn hZ
  have H := HC (n, Z) (by simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using ⟨hn, hZ⟩)
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) hC
  have hnorm : ‖(n, Z)‖ ≤ |n| + ‖Z‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  exact ⟨H.1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hC0) (norm_nonneg Z)),
    H.2.1.trans (mul_le_mul_of_nonneg_left hnorm hC0), H.2.2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartRadialDrift_formula {p : RestartRadialState} (hn : p.1 ^ 2 < 1) :
    restartRadialDrift p =
      p.1 * (restartRadialCurvatureDifference p - 2 * restartRadialRootDifference p) *
        restartQuadraticStrongDerivative p.1 (p.2 0) (p.2 1 - p.2 2) +
      2 * restartRadialCurvatureDifference p * restartQuadratic p.1 (p.2 0) (p.2 1 - p.2 2) +
      2 * restartRadialRootDifference p * (p.2 1 - p.2 2) *
        (restartShearFactor p.1 * restartShearCoupling p.1 * p.2 0 +
          (restartShearCoupling p.1 ^ 2 + restartWallFactor p.1 ^ 2) * (p.2 1 - p.2 2)) +
      2 * Real.sqrt 3 * (p.2 1 + p.2 2) * restartRotationDefect p.1 (p.2 0) (p.2 1 - p.2 2) := by
  unfold restartRadialDrift restartRadialDriftCoefficients
  rw [deriv_restartGramCoefficients hn]
  dsimp [quadraticFromCoefficients, restartGramCoefficients, restartRootCoefficients,
    restartRotationCoefficients, restartQuadraticStrongDerivative, restartQuadratic, restartRotationDefect]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartQuadratic_drift {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1)
    (hp : x t 0 < 0) (hn : x t 2 ^ 2 < 1) :
    HasDerivAt (fun r => restartQuadratic (x r 2) (x r 1) (x r 3 - x r 4))
      (restartRadialDrift (x t 2, restartCenterProjection (x t))) t := by
  apply (hasDerivAt_restartQuadratic_normalized hx hc hn).congr_deriv
  rw [restartRadialDrift_formula hn]
  have hroot := restart_negative_branch_root hc hp
  change -x t 0 = Real.sqrt (restartSectionRadicand (x t 2) (restartCenterProjection (x t))) at hroot
  dsimp only [restartRadialRootDifference]
  rw [← hroot]
  rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_restartRadialDrift {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) :
    ContDiffAt ℝ 3 restartRadialDrift p := by
  have HM := contDiffAt_restartRadialDriftCoefficients hn hr
  have hm (i : Fin 3) := contDiffAt_pi.mp HM i
  unfold restartRadialDrift quadraticFromCoefficients
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.fderiv_restartRadialDrift_apply {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) (w : RestartRadialState) :
    fderiv ℝ restartRadialDrift p w =
      quadraticFromCoefficients (fderiv ℝ restartRadialDriftCoefficients p w) (p.2 0) (p.2 1 - p.2 2) +
      (2 * restartRadialDriftCoefficients p 0 * p.2 0 +
        restartRadialDriftCoefficients p 1 * (p.2 1 - p.2 2)) * w.2 0 +
      (restartRadialDriftCoefficients p 1 * p.2 0 +
        2 * restartRadialDriftCoefficients p 2 * (p.2 1 - p.2 2)) * (w.2 1 - w.2 2) := by
  have HM := (contDiffAt_restartRadialDriftCoefficients hn hr).differentiableAt (by norm_num)
  have hm (i : Fin 3) := hasFDerivAt_pi'.mp HM.hasFDerivAt i
  have hs := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p.2).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have hv := ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) p.2).sub
    (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p.2)).comp p (hasFDerivAt_snd (𝕜 := ℝ))
  have H := (((hm 0).mul (hs.pow 2)).add (((hm 1).mul hs).mul hv)).add ((hm 2).mul (hv.pow 2))
  change HasFDerivAt restartRadialDrift _ p at H
  rw [H.fderiv]
  simp [quadraticFromCoefficients]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.abs_fderiv_restartRadialDrift_apply_le {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) (w : RestartRadialState) :
    |fderiv ℝ restartRadialDrift p w| ≤
      12 * ‖fderiv ℝ restartRadialDriftCoefficients p w‖ * ‖p.2‖ ^ 2 +
        24 * ‖restartRadialDriftCoefficients p‖ * ‖p.2‖ * ‖w.2‖ := by
  rw [fderiv_restartRadialDrift_apply hn hr]
  have hb (Z : RestartCenterState) : |Z 1 - Z 2| ≤ 2 * ‖Z‖ := by
    have H := abs_sub (Z 1) (Z 2)
    have H1 : |Z 1| ≤ ‖Z‖ := norm_le_pi_norm Z 1
    have H2 : |Z 2| ≤ ‖Z‖ := norm_le_pi_norm Z 2
    linarith only [H, H1, H2]
  exact abs_quadratic_tangent_le _ _ (norm_nonneg _) (norm_nonneg _)
    (norm_le_pi_norm p.2 0) (hb _) (norm_le_pi_norm w.2 0) (hb _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_restartRadialDrift_bounds :
    ∃ C ≥ (1 : ℝ), ∀ (n : ℝ) (Z : RestartCenterState),
      (0 ≤ n ∧ n ≤ 1 / 16) → ‖Z‖ ≤ 1 / 16 →
      ContDiffAt ℝ 3 restartRadialDrift (n, Z) ∧
      |restartRadialDrift (n, Z)| ≤ C * (n * ‖Z‖ + ‖Z‖ ^ 2) * restartQuadratic n (Z 0) (Z 1 - Z 2) ∧
      ‖fderiv ℝ (fun W => restartRadialDrift (n, W)) Z‖ ≤ C * (n * ‖Z‖ ^ 2 + ‖Z‖ ^ 3) ∧
      |deriv (fun m => restartRadialDrift (m, Z)) n| ≤ C * ‖Z‖ ^ 3 := by
  obtain ⟨A, hA, HA⟩ := exists_restartRadialDriftCoefficients_bounds
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1) hA
  refine ⟨36 * A, by linarith only [hA], ?_⟩
  intro n Z hn hZ
  have hnabs : |n| ≤ 1 / 16 := by rw [abs_of_nonneg hn.1]; exact hn.2
  have hn2 : n ^ 2 < 1 := by nlinarith only [hn.1, hn.2]
  have hrad := restartSectionRadicand_pos_of_small hnabs hZ
  have Hreg := contDiffAt_restartRadialDrift (p := (n, Z)) hn2 hrad
  have HM := HA n Z hnabs hZ
  rw [abs_of_nonneg hn.1] at HM
  have hQ0 : 0 ≤ restartQuadratic n (Z 0) (Z 1 - Z 2) := add_nonneg (sq_nonneg _) (sq_nonneg _)
  refine ⟨Hreg, ?_, ?_, ?_⟩
  · apply (abs_quadraticFromCoefficients_le (restartRadialDriftCoefficients (n, Z)) (Z 0) (Z 1 - Z 2)).trans
    have Hco := restartQuadratic_coercive hn (Z 0) (Z 1 - Z 2)
    calc
      _ ≤ 2 * (A * (n + ‖Z‖) * ‖Z‖) * (2 * restartQuadratic n (Z 0) (Z 1 - Z 2)) := by
        gcongr
        · positivity [hn.1]
        · exact HM.1
      _ ≤ 36 * A * (n * ‖Z‖ + ‖Z‖ ^ 2) * restartQuadratic n (Z 0) (Z 1 - Z 2) := by
        nlinarith only [mul_nonneg
          (mul_nonneg (mul_nonneg hA0 (add_nonneg hn.1 (norm_nonneg Z))) (norm_nonneg Z)) hQ0]
  · have HD := (Hreg.differentiableAt (by norm_num)).hasFDerivAt.comp Z
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) n Z)
    change HasFDerivAt (fun W => restartRadialDrift (n, W)) _ Z at HD
    rw [HD.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [hn.1])
    intro W
    change |fderiv ℝ restartRadialDrift (n, Z) (0, W)| ≤ _
    have HV : ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (0, W)‖ ≤ A * (n + ‖Z‖) * ‖W‖ := by
      simpa using ((fderiv ℝ restartRadialDriftCoefficients (n, Z)).le_opNorm (0, W)).trans
        (mul_le_mul_of_nonneg_right HM.2.1 (norm_nonneg (0, W)))
    calc
      _ ≤ 12 * ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (0, W)‖ * ‖Z‖ ^ 2 +
          24 * ‖restartRadialDriftCoefficients (n, Z)‖ * ‖Z‖ * ‖W‖ :=
        abs_fderiv_restartRadialDrift_apply_le (p := (n, Z)) hn2 hrad (0, W)
      _ ≤ 12 * (A * (n + ‖Z‖) * ‖W‖) * ‖Z‖ ^ 2 +
          24 * (A * (n + ‖Z‖) * ‖Z‖) * ‖Z‖ * ‖W‖ := by
        gcongr
        exact HM.1
      _ = _ := by ring
  · have HD := (Hreg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt n
      ((hasDerivAt_id' n).prodMk (hasDerivAt_const n Z))
    change HasDerivAt (fun m => restartRadialDrift (m, Z)) _ n at HD
    rw [HD.deriv]
    have H := abs_fderiv_restartRadialDrift_apply_le (p := (n, Z)) hn2 hrad (1, 0)
    change |fderiv ℝ restartRadialDrift (n, Z) (1, 0)| ≤ _ at H
    simp only [norm_zero, mul_zero, add_zero] at H
    calc
      _ ≤ 12 * ‖fderiv ℝ restartRadialDriftCoefficients (n, Z) (1, 0)‖ * ‖Z‖ ^ 2 := H
      _ ≤ 12 * (A * ‖Z‖) * ‖Z‖ ^ 2 := by gcongr; exact HM.2.2
      _ ≤ 36 * A * ‖Z‖ ^ 3 := by nlinarith only [mul_nonneg hA0 (pow_nonneg (norm_nonneg Z) 3)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartSectionQuadratic_nonneg (h t : ℝ) (Z : RestartCenterState) :
    0 ≤ restartSectionQuadratic h t Z := add_nonneg (sq_nonneg _) (sq_nonneg _)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.restartSectionQuadratic_initial (h : ℝ) (Z : RestartCenterState) :
    restartSectionQuadratic h 0 Z = restartQuadratic h (Z 0) (Z 1 - Z 2) := by
  simp only [restartSectionQuadratic, restartSectionStrongWall, restartSectionCenterFlow,
    normalizedMaxCurve_initial, restartCenterProjection_section]
  rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartSectionQuadratic {h t : ℝ} {Z : RestartCenterState}
    (hr : 0 ≤ restartSectionRadicand h Z) (ht : 0 ≤ t)
    (hp : normalizedMaxCurve (restartSectionChart h Z) 0 t 0 < 0)
    (hn : restartSectionStrongWall h t Z ^ 2 < 1) :
    HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t := by
  have H := normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hr) ht
  exact hasDerivAt_restartQuadratic_drift H.1 H.2.1 hp hn

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_restartSectionRadius {h t : ℝ} {Z : RestartCenterState}
    (HD : HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t)
    (HJ : 0 < restartSectionQuadratic h t Z) :
    HasDerivAt (fun s => restartSectionRadius h s Z)
      (restartSectionQuadraticRate h t Z / (2 * restartSectionRadius h t Z)) t :=
  HD.sqrt HJ.ne'

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSectionQuadratic_control :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        0 < restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ h * Real.exp (-2 * t) ∧
        restartSectionStrongWall h t Z ≤ 1 / 16 ∧ ‖restartSectionCenterFlow h t Z‖ ≤ b ∧
        HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t ∧
        |restartSectionQuadraticRate h t Z| ≤ C *
          (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ + ‖restartSectionCenterFlow h t Z‖ ^ 2) *
            restartSectionQuadratic h t Z ∧
        restartSectionQuadratic h 0 Z / 2 ≤ restartSectionQuadratic h t Z ∧
        restartSectionQuadratic h t Z ≤ 2 * restartSectionQuadratic h 0 Z := by
  obtain ⟨A, hA, HA⟩ := exists_restartSection_fastLayer_control
  obtain ⟨B, _, HB⟩ := exists_restartRadialDrift_bounds
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hC : 32 ≤ C := hA.trans hAC
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  refine ⟨C, hC, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ
  have HAh : A * h ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hAC hh.le).trans hCh
  have HAb : A * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hb.1.le) hT).trans hCb
  have HF := HA h b T Z hh HAh hb hT HAb hZ
  have hhsmall : h ≤ 1 / 128 := by nlinarith only [hC, hCh, hh]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rw [abs_of_pos hh]; linarith only [hhsmall]) (by linarith only [hZ, hb.2])
  have Hn (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      0 < restartSectionStrongWall h t Z ∧ restartSectionStrongWall h t Z ≤ 1 / 16 := by
    have HE := Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)
    exact ⟨(HF t ht).1, (HF t ht).2.1.trans
      ((mul_le_mul_of_nonneg_left HE hh.le).trans (by linarith only [hhsmall]))⟩
  have Hz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖restartSectionCenterFlow h t Z‖ ≤ b :=
    (HF t ht).2.2.2.2.le
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun s => restartSectionQuadratic h s Z) (restartSectionQuadraticRate h t Z) t :=
    hasDerivAt_restartSectionQuadratic hrad.le ht.1
      (by linarith only [(HF t ht).2.2.1])
      (by nlinarith only [(Hn t ht).1, (Hn t ht).2])
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |restartSectionQuadraticRate h t Z| ≤ C *
        (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ + ‖restartSectionCenterFlow h t Z‖ ^ 2) *
          restartSectionQuadratic h t Z := by
    have H := (HB _ _ ⟨(Hn t ht).1.le, (Hn t ht).2⟩ ((Hz t ht).trans hb.2)).2.1
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBC (add_nonneg
        (mul_nonneg (Hn t ht).1.le (norm_nonneg _)) (sq_nonneg _)))
      (restartSectionQuadratic_nonneg h t Z))
  have HG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |restartSectionQuadraticRate h t Z| ≤ C * (h * Real.exp (-2 * t) + b) * restartSectionQuadratic h t Z := by
    have hr1 : ‖restartSectionCenterFlow h t Z‖ ≤ 1 := (Hz t ht).trans (by linarith only [hb.2])
    have Hcoeff : restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ +
        ‖restartSectionCenterFlow h t Z‖ ^ 2 ≤ h * Real.exp (-2 * t) + b := by
      have Hs : ‖restartSectionCenterFlow h t Z‖ ^ 2 ≤ ‖restartSectionCenterFlow h t Z‖ := by
        nlinarith only [mul_nonneg (norm_nonneg (restartSectionCenterFlow h t Z)) (sub_nonneg.mpr hr1)]
      have Hn' := mul_le_mul_of_nonneg_left hr1 (Hn t ht).1.le
      have HE : restartSectionStrongWall h t Z ≤ h * Real.exp (-2 * t) := (HF t ht).2.1
      nlinarith only [Hs, Hn', HE, Hz t ht]
    exact (HR t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Hcoeff hC0) (restartSectionQuadratic_nonneg h t Z))
  have Hcomp := scalar_clock_comparison HD (fun t _ => hasDerivAt_restartFastBudget C h b t) HG
  intro t ht
  have HE : restartFastBudget C h b t ≤ 1 / 4 :=
    (restartFastBudget_le hC0 hh.le hb.1.le ht.2).trans (by linarith only [hCh, hCb])
  have Hexp := (Real.exp_le_exp.mpr HE).trans exp_one_quarter_lt_two.le
  have Hinv : 1 / 2 ≤ Real.exp (-restartFastBudget C h b t) := by
    have H := mul_le_mul_of_nonneg_right Hexp (Real.exp_pos (-restartFastBudget C h b t)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
    linarith only [H]
  have HC := Hcomp t ht
  rw [restartFastBudget_zero, sub_zero] at HC
  refine ⟨(Hn t ht).1, (HF t ht).2.1, (Hn t ht).2, Hz t ht, HD t ht, HR t ht, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_left Hinv (restartSectionQuadratic_nonneg h 0 Z)
    linarith only [H, HC.1]
  · exact HC.2.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left Hexp (restartSectionQuadratic_nonneg h 0 Z))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartSectionRadius_value_error :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        |restartSectionRadius h t Z - restartSectionRadius h 0 Z| ≤ C * h * b ^ 2 + 2 * C * b ^ 3 * t ∧
        |restartRadialNorm (restartSectionCenterFlow h t Z) - restartSectionRadius h 0 Z| ≤
          C * h * b ^ 2 + 2 * C * b ^ 3 * t + 24 * h * b * Real.exp (-2 * t) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionQuadratic_control
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  refine ⟨C, hC, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ
  have H := HC h b T Z hh hCh hb hT hCb hZ
  have hb0 : 0 ≤ b := hb.1.le
  have hcoord (W : RestartCenterState) : |W 1 - W 2| ≤ 2 * ‖W‖ := by
    have H1 : |W 1| ≤ ‖W‖ := norm_le_pi_norm W 1
    have H2 : |W 2| ≤ ‖W‖ := norm_le_pi_norm W 2
    linarith only [abs_sub (W 1) (W 2), H1, H2]
  have hcoords (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |restartSectionCenterFlow h t Z 0| ≤ b ∧
        |restartSectionCenterFlow h t Z 1 - restartSectionCenterFlow h t Z 2| ≤ 2 * b :=
    ⟨(norm_le_pi_norm (restartSectionCenterFlow h t Z) 0).trans (H t ht).2.2.2.1,
      (hcoord _).trans (mul_le_mul_of_nonneg_left (H t ht).2.2.2.1 (by norm_num))⟩
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : restartSectionRadius h t Z ≤ 4 * b :=
    sqrt_restartQuadratic_le_radius ⟨(H t ht).1.le, (H t ht).2.2.1⟩ hb0 (hcoords t ht).1 (hcoords t ht).2
  have Hvalue : ∀ t ∈ Icc (0 : ℝ) T,
      |restartSectionRadius h t Z - restartSectionRadius h 0 Z| ≤ C * h * b ^ 2 + 2 * C * b ^ 3 * t := by
    by_cases H0 : restartSectionQuadratic h 0 Z = 0
    · intro t ht
      have Ht : restartSectionQuadratic h t Z = 0 := by
        have Hu := (H t ht).2.2.2.2.2.2.2
        rw [H0] at Hu
        linarith only [Hu, restartSectionQuadratic_nonneg h t Z]
      simp only [restartSectionRadius, H0, Ht, Real.sqrt_zero, sub_self, abs_zero]
      positivity [ht.1]
    have Hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 < restartSectionQuadratic h t Z := by
      have Hinit := lt_of_le_of_ne (restartSectionQuadratic_nonneg h 0 Z) (Ne.symm H0)
      linarith only [Hinit, (H t ht).2.2.2.2.2.2.1]
    have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
      hasDerivAt_restartSectionRadius (H t ht).2.2.2.2.1 (Hpos t ht)
    have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        |restartSectionQuadraticRate h t Z / (2 * restartSectionRadius h t Z)| ≤
          (2 * C) * ((h * b ^ 2) * Real.exp (-2 * t) + b ^ 3) := by
      have hn0 : 0 ≤ restartSectionStrongWall h t Z := (H t ht).1.le
      have hRpos : 0 < restartSectionRadius h t Z := Real.sqrt_pos.mpr (Hpos t ht)
      have hnorm : ‖restartSectionCenterFlow h t Z‖ ≤ b := (H t ht).2.2.2.1
      have hsq : restartSectionRadius h t Z ^ 2 = restartSectionQuadratic h t Z :=
        Real.sq_sqrt (restartSectionQuadratic_nonneg h t Z)
      have Hcoeff : restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ +
          ‖restartSectionCenterFlow h t Z‖ ^ 2 ≤ restartSectionStrongWall h t Z * b + b ^ 2 := by
        have Hs := mul_self_le_mul_self (norm_nonneg (restartSectionCenterFlow h t Z)) hnorm
        nlinarith only [Hs, mul_le_mul_of_nonneg_left hnorm hn0]
      have Hrate : |restartSectionQuadraticRate h t Z / (2 * restartSectionRadius h t Z)| ≤
          2 * C * (restartSectionStrongWall h t Z * b ^ 2 + b ^ 3) := by
        rw [abs_div, abs_of_pos (mul_pos (by norm_num) hRpos)]
        apply (div_le_iff₀ (mul_pos (by norm_num) hRpos)).mpr
        calc
          _ ≤ C * (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ +
              ‖restartSectionCenterFlow h t Z‖ ^ 2) * restartSectionQuadratic h t Z :=
            (H t ht).2.2.2.2.2.1
          _ = C * (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ +
              ‖restartSectionCenterFlow h t Z‖ ^ 2) * (restartSectionRadius h t Z * restartSectionRadius h t Z) := by
            rw [← hsq]
            ring
          _ ≤ C * (restartSectionStrongWall h t Z * b + b ^ 2) * (4 * b * restartSectionRadius h t Z) := by
            gcongr
            exact HR t ht
          _ = _ := by ring
      calc
        _ ≤ 2 * C * (restartSectionStrongWall h t Z * b ^ 2 + b ^ 3) := Hrate
        _ ≤ 2 * C * ((h * Real.exp (-2 * t)) * b ^ 2 + b ^ 3) := by
          gcongr
          exact (H t ht).2.1
        _ = _ := by ring
    have HP := abs_sub_le_of_deriv_primitive HD
      (fun t _ => hasDerivAt_restartFastBudget (2 * C) (h * b ^ 2) (b ^ 3) t) HB
    intro t ht
    have HV := HP t ht
    rw [restartFastBudget_zero, sub_zero] at HV
    have HE := restartFastBudget_le (by positivity : 0 ≤ 2 * C)
      (by positivity : 0 ≤ h * b ^ 2) (pow_nonneg hb0 3) (T := t) le_rfl
    exact HV.trans (by nlinarith only [HE])
  intro t ht
  refine ⟨Hvalue t ht, ?_⟩
  have Htail := sqrt_restartQuadratic_tail ⟨(H t ht).1.le, (H t ht).2.2.1⟩ hb0 (hcoords t ht).1 (hcoords t ht).2
  change |restartSectionRadius h t Z - restartRadialNorm (restartSectionCenterFlow h t Z)| ≤
    24 * restartSectionStrongWall h t Z * b at Htail
  calc
    _ ≤ |restartRadialNorm (restartSectionCenterFlow h t Z) - restartSectionRadius h t Z| +
        |restartSectionRadius h t Z - restartSectionRadius h 0 Z| := abs_sub_le _ _ _
    _ ≤ 24 * restartSectionStrongWall h t Z * b + (C * h * b ^ 2 + 2 * C * b ^ 3 * t) := by
      rw [abs_sub_comm]
      exact add_le_add Htail (Hvalue t ht)
    _ ≤ C * h * b ^ 2 + 2 * C * b ^ 3 * t + 24 * h * b * Real.exp (-2 * t) := by
      nlinarith only [mul_le_mul_of_nonneg_right (H t ht).2.1 hb0]

end
end

private theorem BianchiIX.exists_restartSection_radial_cutoff_error :
    ∃ C ≥ (32 : ℝ), ∀ (h C₀ ρ q : ℝ),
      0 < h → C * h ≤ 1 / 4 → 0 < C₀ → (0 < ρ ∧ ρ ≤ 1) → 0 ≤ q →
      2 * C₀ * ρ ≤ 1 / 16 → C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 →
      ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ →
        let T := q / 2 * Real.log (1 / ρ)
        T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
        |restartRadialPhase (restartSectionCenterFlow h T Z) - restartReferenceRadialPhase h Z| ≤
          4 * C * C₀ ^ 2 * h * ρ ^ 2 + 16 * C * C₀ ^ 3 * ρ ^ 3 * T + 48 * C₀ * h * ρ ^ (q + 1) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionRadius_value_error
  refine ⟨C, hC, ?_⟩
  intro h C₀ ρ q hh hCh hC₀ hρ hq hb hCb Z hZ
  have hρ0 : 0 < ρ := hρ.1
  let b := 2 * C₀ * ρ
  let T := q / 2 * Real.log (1 / ρ)
  have hb0 : 0 < b := by dsimp only [b]; positivity
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hq (by norm_num))
    (Real.log_nonneg ((le_div_iff₀ hρ.1).mpr (by linarith only [hρ.2])))
  have hZb : ‖Z‖ ≤ b / 2 := by dsimp only [b]; linarith only [hZ]
  have HV := (HC h b T Z hh hCh ⟨hb0, hb⟩ hT hCb hZb T ⟨hT, le_rfl⟩).2
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh]) (by linarith only [hZ, hb])
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have he : Real.exp (-2 * T) = ρ ^ q := by
    rw [Real.rpow_def_of_pos hρ.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  have Hnorm :
      |restartRadialPhase (restartSectionCenterFlow h T Z) - restartReferenceRadialPhase h Z| ≤
        |restartRadialNorm (restartSectionCenterFlow h T Z) - restartSectionRadius h 0 Z| := by
    dsimp only [restartRadialPhase, restartReferenceRadialPhase, restartSectionRadius]
    rw [restartSectionQuadratic_initial, ← sub_div, abs_div, abs_of_pos hsqrt]
    apply (div_le_iff₀ hsqrt).mpr
    nlinarith only [mul_nonneg
      (abs_nonneg (restartRadialNorm (restartSectionCenterFlow h T Z) -
        Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)))) (sub_nonneg.mpr hsqrt1)]
  refine ⟨hdom, (Hnorm.trans HV).trans_eq ?_⟩
  rw [he, Real.rpow_add hρ0, Real.rpow_one]
  dsimp only [b]
  ring

/-- The quadratic radial value error has a constant chosen before the cutoff exponent. -/
theorem solution :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ C₀ : ℝ, 0 < C₀ → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ ρstar : ℝ, 0 < ρstar ∧ ∀ ρ ∈ Ioc (0 : ℝ) ρstar,
          ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ →
            let T := q / 2 * Real.log (1 / ρ)
            T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            |restartRadialPhase (restartSectionCenterFlow h T Z) - restartReferenceRadialPhase h Z| ≤
              K * ρ ^ 2 := by
  obtain ⟨C, hC, HC⟩ := exists_restartSection_radial_cutoff_error
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  let hstar := 1 / (4 * C)
  have hstarpos : 0 < hstar := by dsimp only [hstar]; positivity
  refine ⟨hstar, hstarpos, ?_⟩
  intro h hh C₀ hC₀
  have hhpos : 0 < h := hh.1
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    nlinarith only [H]
  let K := 4 * C * C₀ ^ 2 * h + C₀ ^ 2 + 48 * C₀ * h
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨ρstar, hρstar, Hbudget⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_cutoff_budget C C₀ q)
  refine ⟨ρstar, hρstar, ?_⟩
  intro ρ hρ Z hZ
  have Hb := Hbudget hρ
  have HR := HC h C₀ ρ q hhpos hCh hC₀ Hb.1 (by linarith only [hq]) Hb.2.1 Hb.2.2 Z hZ
  refine ⟨HR.1, HR.2.trans ?_⟩
  have Htime := mul_le_mul_of_nonneg_right Hb.2.2
    (by positivity : 0 ≤ 8 * C₀ ^ 2 * ρ ^ 2)
  have Hpower : ρ ^ (q + 1) ≤ ρ ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge Hb.1.1 Hb.1.2
      (by linarith only [hq] : (2 : ℝ) ≤ q + 1)
  have Htail := mul_le_mul_of_nonneg_left Hpower (by positivity : 0 ≤ 48 * C₀ * h)
  dsimp only [K]
  nlinarith only [Htime, Htail]
