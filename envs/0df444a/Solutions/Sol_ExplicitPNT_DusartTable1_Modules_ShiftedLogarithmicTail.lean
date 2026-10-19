-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.ShiftedLogarithmicTail
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:34:28.380457+00:00
-- url     : https://prove2.me/submissions/02bfdf93-8674-4e29-9bf4-343ffdfd00ef

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region
import Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_dusart_psi_433_20261014_PsiComparison
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_Region100
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ZeroCountIncrement
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ZeroSumPrimitive

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex Set MeasureTheory
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem log_hundred_lower : (23 / 5 : ℝ) < Real.log 100 :=
  ExplicitPNT.DusartTable1.Modules.Region100.1

private theorem finite_zero_count_increment_bound : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H t : ℝ) (hH : 4 ≤ H) (hHt : H ≤ t) (hγ : ∀ ρ ∈ Z, H < ρ.im),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      DusartSmoothing.RvM.countingMain t - DusartSmoothing.RvM.countingMain H +
      9 * Real.log (t + 5) + 9 * Real.log (H + 5) + 158 :=
  ExplicitPNT.DusartTable1.Modules.ZeroCountIncrement.2

private theorem finite_zero_sum_le_primitive : ∀ (Z : Finset ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ ρ ∈ Z, a ≤ ρ.im ∧ ρ.im ≤ b)
    (g d W J : ℝ → ℝ)
    (hcont : ContinuousOn d (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (d t) t)
    (hJ : ∀ t ∈ uIcc a b, HasDerivAt J (W t * d t) t)
    (hneg : ∀ t ∈ Icc a b, d t ≤ 0)
    (hcount : ∀ t ∈ Icc a b,
      finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ W t)
    (hg : 0 ≤ g b) (hend : g b * W b ≤ J b),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * g ρ.im) ≤ J a :=
  ExplicitPNT.DusartTable1.Modules.ZeroSumPrimitive

private theorem log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  apply (Real.log_le_iff_le_exp (by positivity)).2
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.exp_one_gt_d9
    norm_num at hh ⊢
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he 2
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith [Real.pi_lt_d2]

private theorem finite_positive_inverse_cube_tail_shifted (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H : ℝ) (hH : 1000 ≤ H) (hγ : ∀ ρ ∈ Z, H < ρ.im) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (2 * Real.log (H / (2 * Real.pi)) + 1) / (8 * Real.pi * H^2) +
      (18 * Real.log H + 179) / H^3 := by
  classical
  have hH0 : 0 < H := by linarith
  let k : ℝ := 1 / (2 * Real.pi)
  let c : ℝ := Real.log (2 * Real.pi) + 1
  let D : ℝ := -k * H * (Real.log H - c) + 9 * Real.log H + 176
  let g : ℝ → ℝ := fun t => 1 / t^3
  let d : ℝ → ℝ := fun t => -3 / t^4
  let W : ℝ → ℝ := fun t => k * t * (Real.log t - c) + 9 * Real.log t + D
  let J : ℝ → ℝ := fun t =>
    k * ((3 / 2 : ℝ) * (Real.log t - c) + 3 / 4) / t^2 +
      (9 * Real.log t + (3 + D)) / t^3
  have hk : 0 < k := by dsimp [k]; positivity
  have hc : c ≤ 3 := by dsimp [c]; linarith [log_two_pi_le_two]
  have hF (t : ℝ) (ht : 0 < t) :
      DusartSmoothing.RvM.countingMain t = k * t * (Real.log t - c) := by
    unfold DusartSmoothing.RvM.countingMain
    rw [Real.log_div ht.ne' (by positivity)]
    dsimp [k, c]
    ring
  have hlog (t : ℝ) (ht : H ≤ t) : Real.log (t + 5) ≤ Real.log t + 1 := by
    have ht0 : 0 < t := hH0.trans_le ht
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh
      exact hh
    calc
      _ ≤ Real.log (2 * t) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht0.ne'
      _ ≤ _ := by linarith
  have hJH : J H =
      (2 * Real.log (H / (2 * Real.pi)) + 1) / (8 * Real.pi * H^2) +
      (18 * Real.log H + 179) / H^3 := by
    dsimp [J, D, c, k]
    rw [Real.log_div hH0.ne' (by positivity)]
    field_simp [hH0.ne', Real.pi_ne_zero]
    ring
  by_cases hn : Z.Nonempty
  · let b : ℝ := max H (Z.sup' hn Complex.im)
    have hab : H ≤ b := le_max_left _ _
    have hb0 : 0 < b := hH0.trans_le hab
    have hγb (ρ : ℂ) (hρ : ρ ∈ Z) : ρ.im ≤ b :=
      (Finset.le_sup' Complex.im hρ).trans (le_max_right _ _)
    have hcont : ContinuousOn d (Icc H b) := by
      intro t ht
      have ht0 : 0 < t := hH0.trans_le ht.1
      apply ContinuousAt.continuousWithinAt
      dsimp [d]
      fun_prop (disch := positivity)
    have hW : ContinuousOn W (Icc H b) := by
      intro t ht
      have hn : t ≠ 0 := (hH0.trans_le ht.1).ne'
      apply ContinuousAt.continuousWithinAt
      dsimp [W]
      fun_prop (disch := assumption)
    have hd : ∀ t ∈ Icc H b, HasDerivAt g (d t) t := by
      intro t ht
      have hn : t ≠ 0 := (hH0.trans_le ht.1).ne'
      have hh := ((hasDerivAt_id t).pow 3).inv (pow_ne_zero 3 hn)
      have he : (id ^ 3 : ℝ → ℝ)⁻¹ = g := by funext u; simp [g]
      rw [he] at hh
      exact hh.congr_deriv (by dsimp [d]; field_simp [hn] <;> ring)
    have hJ : ∀ t ∈ uIcc H b, HasDerivAt J (W t * d t) t := by
      intro t ht
      rw [uIcc_of_le hab] at ht
      have hn : t ≠ 0 := (hH0.trans_le ht.1).ne'
      have h1 := (((((Real.hasDerivAt_log hn).sub_const c).const_mul (3 / 2)).add_const
        (3 / 4)).const_mul k).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 hn)
      have h2 := (((Real.hasDerivAt_log hn).const_mul 9).add_const (3 + D)).div
        ((hasDerivAt_id t).pow 3) (pow_ne_zero 3 hn)
      apply (h1.add h2).congr_deriv
      dsimp [W, d]
      field_simp [hn]
      ring
    have hcount : ∀ t ∈ Icc H b,
        finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ W t := by
      intro t ht
      have hi := finite_zero_count_increment_bound Z hZ H t (by linarith) ht.1 hγ
      rw [hF t (hH0.trans_le ht.1), hF H hH0] at hi
      have hlt := hlog t ht.1
      have hlH := hlog H le_rfl
      dsimp [W, D]
      linarith only [hi, hlt, hlH]
    have hend : g b * W b ≤ J b := by
      have hlogb : 4 ≤ Real.log b := by
        have hh := log_hundred_lower.trans_le
          (Real.log_le_log (by norm_num) (show (100 : ℝ) ≤ b by linarith))
        linarith
      have hdiff : 0 ≤ Real.log b - c := by linarith only [hlogb, hc]
      have hnonneg : 0 ≤ k * ((1 / 2 : ℝ) * (Real.log b - c) + 3 / 4) / b^2 + 3 / b^3 := by
        positivity
      have he : J b - g b * W b =
          k * ((1 / 2 : ℝ) * (Real.log b - c) + 3 / 4) / b^2 + 3 / b^3 := by
        dsimp [J, g, W]
        field_simp [hb0.ne']
        ring
      linarith only [he, hnonneg]
    have hh := finite_zero_sum_le_primitive Z H b hab
      (fun ρ hρ => ⟨(hγ ρ hρ).le, hγb ρ hρ⟩) g d W J hcont hW hd hJ
      (fun t _ => by dsimp [d]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
      hcount (by dsimp [g]; positivity) hend
    exact hh.trans_eq hJH
  · have he : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, Finset.sum_empty]
    have hl : 0 ≤ Real.log (H / (2 * Real.pi)) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ (by positivity)).2
      linarith [Real.pi_lt_four]
    have hlH : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    positivity

end ExplicitPNT.DusartTable1

theorem solution :
(
    Real.log (2 * Real.pi) ≤ 2
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H : ℝ) (hH : 1000 ≤ H) (hγ : ∀ ρ ∈ Z, H < ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (2 * Real.log (H / (2 * Real.pi)) + 1) / (8 * Real.pi * H^2) +
      (18 * Real.log H + 179) / H^3
) := by
  exact ⟨log_two_pi_le_two, finite_positive_inverse_cube_tail_shifted⟩
