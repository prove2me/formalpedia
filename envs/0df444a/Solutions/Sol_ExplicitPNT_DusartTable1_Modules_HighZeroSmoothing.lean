-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.HighZeroSmoothing
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:40:19.656979+00:00
-- url     : https://prove2.me/submissions/054c9a07-3224-4f9a-8638-349b7842c921

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ImprovedRegion
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_AbsoluteNumericalZeroTail

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem zeta_seven_eighths : ∀ (s : ℂ) (hs : (7 / 8 : ℝ) < s.re),
    riemannZeta s ≠ 0 :=
  ExplicitPNT.DusartTable1.Modules.ImprovedRegion.1

private theorem finite_absolute_inverse_cube_tail_H : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < |ρ.im|),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤
      (8 / 10^25 : ℝ) :=
  ExplicitPNT.DusartTable1.Modules.AbsoluteNumericalZeroTail.1

private theorem high_smoothed_zero_sum_bound (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z) :
    (∑' ρ : StrictHighAbsoluteZero (2445999556030 : ℝ),
      ‖(DusartSmoothing.RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      (32 / 10^25 : ℝ) * z^(23 / 8 : ℝ) / h^2 := by
  classical
  have hz : 0 < z := by linarith
  let B : ℝ := 4 * z^(23 / 8 : ℝ) / h^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (ρ : StrictHighAbsoluteZero (2445999556030 : ℝ)) :
      ‖(DusartSmoothing.RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖ ≤
        B * ((DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^3)) := by
    have hρ := ρ.property.1
    have hβ : ρ.val.re ≤ (7 / 8 : ℝ) := by
      by_contra! hβ
      exact zeta_seven_eighths ρ.val hβ hρ.1
    have hi : 0 < |ρ.val.im| := by linarith [ρ.property.2]
    have hp (y : ℝ) (hy : y ∈ Set.Icc a (a + 2 * h)) :
        ‖(y : ℂ)^ρ.val‖ ≤ z^(7 / 8 : ℝ) := by
      have hy0 : 0 < y := by linarith [hy.1]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      exact (Real.rpow_le_rpow_of_exponent_le (ha.trans hy.1) hβ).trans
        (Real.rpow_le_rpow hy0.le (hy.2.trans haz) (by norm_num))
    have hk := norm_smoothedZeroKernel_high a h (z^(7 / 8 : ℝ)) (by linarith) hh
      (Real.rpow_nonneg hz.le _) ρ.val hi hp
    have hzpow : z^(7 / 8 : ℝ) * z^2 = z^(23 / 8 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_add hz]
      norm_num
    have hk' : ‖smoothedZeroKernel a h ρ.val‖ ≤ B * (1 / |ρ.val.im|^3) := by
      calc
        _ ≤ 4 * z^(7 / 8 : ℝ) * z^2 / (h^2 * |ρ.val.im|^3) := by
          apply hk.trans
          gcongr
        _ = _ := by dsimp [B]; rw [← hzpow]; ring
    rw [norm_mul, Complex.norm_natCast]
    have hm := mul_le_mul_of_nonneg_left hk' (Nat.cast_nonneg (DusartSmoothing.RvM.zeroMult ρ.val))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
  apply Real.tsum_le_of_sum_le (fun ρ => norm_nonneg _)
  intro S
  let Z : Finset ℂ := S.image (fun ρ : StrictHighAbsoluteZero (2445999556030 : ℝ) => ρ.val)
  have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
    exact τ.property.1
  have hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < |ρ.im| := by
    intro ρ hρ
    obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
    exact τ.property.2
  have hc := finite_absolute_inverse_cube_tail_H Z hZ hγ
  dsimp [Z] at hc
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hc
  calc
    _ ≤ ∑ ρ ∈ S, B * ((DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^3)) :=
      Finset.sum_le_sum (fun ρ _ => hterm ρ)
    _ = B * (∑ ρ ∈ S, (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^3)) := by rw [Finset.mul_sum]
    _ ≤ B * (8 / 10^25 : ℝ) := mul_le_mul_of_nonneg_left hc hB
    _ = _ := by dsimp [B]; ring

end ExplicitPNT.DusartTable1

theorem solution :
∀ (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z),
    (∑' ρ : StrictHighAbsoluteZero (2445999556030 : ℝ),
      ‖(DusartSmoothing.RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      (32 / 10^25 : ℝ) * z^(23 / 8 : ℝ) / h^2 := by
  exact high_smoothed_zero_sum_bound
