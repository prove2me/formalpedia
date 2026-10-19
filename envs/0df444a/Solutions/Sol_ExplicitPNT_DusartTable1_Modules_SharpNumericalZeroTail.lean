-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.SharpNumericalZeroTail
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:36:36.488903+00:00
-- url     : https://prove2.me/submissions/efa04b31-f798-4e76-96c4-0004b66b0303

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ShiftedLogarithmicTail
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_NumericalZeroTail

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem finite_positive_inverse_cube_tail_shifted : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H : ℝ) (hH : 1000 ≤ H) (hγ : ∀ ρ ∈ Z, H < ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (2 * Real.log (H / (2 * Real.pi)) + 1) / (8 * Real.pi * H^2) +
      (18 * Real.log H + 179) / H^3 :=
  ExplicitPNT.DusartTable1.Modules.ShiftedLogarithmicTail.2

private theorem log_le_integer_of_certificate : ∀ (T : ℝ) (n : ℕ) (hT : 0 < T)
    (hnum : T ≤ (2718281828 / 10^9 : ℝ)^n),
    Real.log T ≤ (n : ℝ) :=
  ExplicitPNT.DusartTable1.Modules.NumericalZeroTail.1

private theorem positive_inverse_cube_tsum_shifted (T : ℝ) (hT : 1000 ≤ T) :
    (∑' ρ : StrictHighPositiveZero T,
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (2 * Real.log (T / (2 * Real.pi)) + 1) / (8 * Real.pi * T^2) +
      (18 * Real.log T + 179) / T^3 := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro ρ
    have hi : 0 < ρ.val.im := by linarith [ρ.property.2]
    positivity
  · intro S
    let Z : Finset ℂ := S.image (fun ρ : StrictHighPositiveZero T => ρ.val)
    have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact ⟨τ.property.1, by linarith [τ.property.2]⟩
    have hγ : ∀ ρ ∈ Z, T < ρ.im := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.2
    have hh := finite_positive_inverse_cube_tail_shifted Z hZ T hT hγ
    dsimp [Z] at hh
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hh
    exact hh

private theorem shifted_tail_bound_of_log_bound (T L : ℝ) (hT : 0 < T) (hL : 1 ≤ L)
    (hl : Real.log T ≤ L) :
    (2 * Real.log (T / (2 * Real.pi)) + 1) / (8 * Real.pi * T^2) +
      (18 * Real.log T + 179) / T^3 ≤
      (2 * (L - 1) + 1) / (24 * T^2) + (18 * L + 179) / T^3 := by
  have hπ : 1 ≤ Real.log (2 * Real.pi) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he := Real.exp_one_lt_d9
    norm_num at he
    linarith [Real.pi_gt_three]
  have hn : 2 * Real.log (T / (2 * Real.pi)) + 1 ≤ 2 * (L - 1) + 1 := by
    rw [Real.log_div hT.ne' (by positivity)]
    linarith
  apply add_le_add
  · calc
      _ ≤ (2 * (L - 1) + 1) / (8 * Real.pi * T^2) :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ ≤ (2 * (L - 1) + 1) / (24 * T^2) := by
        apply div_le_div_of_nonneg_left (by linarith) (by positivity)
        nlinarith [Real.pi_gt_three, sq_pos_of_pos hT]
  · apply div_le_div_of_nonneg_right _ (by positivity)
    linarith

private theorem positive_inverse_cube_tail_T0_sharp :
    (∑' ρ : StrictHighPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (9 / 10^13 : ℝ) := by
  have hh := positive_inverse_cube_tsum_shifted (566245491 / 500) (by norm_num)
  have hl := log_le_integer_of_certificate (566245491 / 500) 14 (by norm_num) (by norm_num)
  norm_num at hl
  have hb := shifted_tail_bound_of_log_bound (566245491 / 500) 14 (by norm_num) (by norm_num) hl
  apply hh.trans (hb.trans _)
  norm_num

private theorem positive_inverse_cube_tail_H_sharp :
    (∑' ρ : StrictHighPositiveZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (4 / 10^25 : ℝ) := by
  have hh := positive_inverse_cube_tsum_shifted 2445999556030 (by norm_num)
  have hl := log_le_integer_of_certificate 2445999556030 29 (by norm_num) (by norm_num)
  norm_num at hl
  have hb := shifted_tail_bound_of_log_bound 2445999556030 29 (by norm_num) (by norm_num) hl
  apply hh.trans (hb.trans _)
  norm_num

private theorem finite_positive_inverse_cube_tail_H_sharp (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < ρ.im) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (4 / 10^25 : ℝ) := by
  have hh := finite_positive_inverse_cube_tail_shifted Z hZ 2445999556030 (by norm_num) hγ
  have hl := log_le_integer_of_certificate 2445999556030 29 (by norm_num) (by norm_num)
  norm_num at hl
  have hb := shifted_tail_bound_of_log_bound 2445999556030 29 (by norm_num) (by norm_num) hl
  apply hh.trans (hb.trans _)
  norm_num

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (T : ℝ) (hT : 1000 ≤ T),
    (∑' ρ : StrictHighPositiveZero T,
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (2 * Real.log (T / (2 * Real.pi)) + 1) / (8 * Real.pi * T^2) +
      (18 * Real.log T + 179) / T^3
) ∧
(
    ∀ (T L : ℝ) (hT : 0 < T) (hL : 1 ≤ L)
    (hl : Real.log T ≤ L),
    (2 * Real.log (T / (2 * Real.pi)) + 1) / (8 * Real.pi * T^2) +
      (18 * Real.log T + 179) / T^3 ≤
      (2 * (L - 1) + 1) / (24 * T^2) + (18 * L + 179) / T^3
) ∧
(
    (∑' ρ : StrictHighPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (9 / 10^13 : ℝ)
) ∧
(
    (∑' ρ : StrictHighPositiveZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (4 / 10^25 : ℝ)
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (4 / 10^25 : ℝ)
) := by
  exact ⟨positive_inverse_cube_tsum_shifted, shifted_tail_bound_of_log_bound, positive_inverse_cube_tail_T0_sharp, positive_inverse_cube_tail_H_sharp, finite_positive_inverse_cube_tail_H_sharp⟩
