-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.PowerQuarterSmoothed
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:32:20.435714+00:00
-- url     : https://prove2.me/submissions/9e2f241c-ad60-43c2-80fe-df98c181c156

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem zeta_seven_eighths : ∀ (s : ℂ) (hs : (7 / 8 : ℝ) < s.re),
    riemannZeta s ≠ 0 :=
  ExplicitPNT.DusartTable1.Modules.ImprovedRegion.1

private theorem finite_absolute_split_kernel_bound : ∀ (T : ℝ) (hT : 4 ≤ T) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) *
      min (1 / |ρ.im|) (4 * T^2 / |ρ.im|^3)) ≤ (1328 / 7 : ℝ) * T^(1 / 4 : ℝ) :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.2.2

private theorem smoothed_zero_norm_quarter_bound (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z) (hT : 4 ≤ z / h) :
    (∑' ρ : DusartSmoothing.NontrivialZetaZero,
      ‖(DusartSmoothing.RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ) := by
  classical
  have hz : 0 < z := by linarith
  let M : ℝ := z^(7 / 8 : ℝ)
  have hM : 0 ≤ M := Real.rpow_nonneg hz.le _
  let T : ℝ := z / h
  let W : ℝ → ℝ := fun t => min (1 / t) (4 * T^2 / t^3)
  have hterm (ρ : DusartSmoothing.NontrivialZetaZero) :
      ‖(DusartSmoothing.RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖ ≤
        M * ((DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * W |ρ.val.im|) := by
    have hρ := ρ.property
    have hβ : ρ.val.re ≤ (7 / 8 : ℝ) := by
      by_contra! hβ
      exact zeta_seven_eighths ρ.val hβ hρ.1
    have hi : 0 < |ρ.val.im| := by
      have ht := DusartSmoothing.RvM.nontrivial_zero_abs_height ρ.val hρ
      linarith [Real.pi_pos]
    have hp (y : ℝ) (hy : y ∈ Set.Icc a (a + 2 * h)) : ‖(y : ℂ)^ρ.val‖ ≤ M := by
      have hy0 : 0 < y := by linarith [hy.1]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      exact (Real.rpow_le_rpow_of_exponent_le (ha.trans hy.1) hβ).trans
        (Real.rpow_le_rpow hy0.le (hy.2.trans haz) (by norm_num))
    have hlow := norm_smoothedZeroKernel_low a h M hh hM ρ.val hρ.2.1 hi hp
    have hhigh := norm_smoothedZeroKernel_high a h M (by linarith) hh hM ρ.val hi hp
    have hk : ‖smoothedZeroKernel a h ρ.val‖ ≤ M * W |ρ.val.im| := by
      dsimp [W]
      rw [mul_min_of_nonneg _ _ hM]
      apply le_min
      · simpa only [div_eq_mul_inv, one_mul] using hlow
      · calc
          _ ≤ 4 * M * z^2 / (h^2 * |ρ.val.im|^3) := by
            apply hhigh.trans
            gcongr
          _ = M * (4 * T^2 / |ρ.val.im|^3) := by dsimp [T]; ring
    rw [norm_mul, Complex.norm_natCast]
    have hm := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg (DusartSmoothing.RvM.zeroMult ρ.val))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
  apply Real.tsum_le_of_sum_le (fun ρ => norm_nonneg _)
  intro S
  let Z : Finset ℂ := S.image (fun ρ : DusartSmoothing.NontrivialZetaZero => ρ.val)
  have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    obtain ⟨τ, _, he⟩ := Finset.mem_image.mp hρ
    exact he ▸ τ.property
  have hc := finite_absolute_split_kernel_bound T hT Z hZ
  dsimp [Z] at hc
  rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hc
  have hp : M * T^(1 / 4 : ℝ) = z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ) := by
    dsimp [M, T]
    rw [Real.div_rpow hz.le hh.le, ← mul_div_assoc, ← Real.rpow_add hz]
    norm_num
  calc
    _ ≤ ∑ ρ ∈ S, M * ((DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * W |ρ.val.im|) :=
      Finset.sum_le_sum (fun ρ _ => hterm ρ)
    _ = M * (∑ ρ ∈ S, (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * W |ρ.val.im|) := by rw [Finset.mul_sum]
    _ ≤ M * ((1328 / 7 : ℝ) * T^(1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hc hM
    _ = (1328 / 7 : ℝ) * (z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ)) := by
      rw [show M * ((1328 / 7 : ℝ) * T^(1 / 4 : ℝ)) =
        (1328 / 7 : ℝ) * (M * T^(1 / 4 : ℝ)) by ring, hp]
    _ ≤ 192 * (z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ)) := by gcongr; norm_num
    _ = _ := by ring

private theorem double_average_quarter_bound (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z) (hT : 4 ≤ z / h) :
    |doubleBoxAverage Chebyshev.psi a h - (a + h)| ≤
      2 + 192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ) + 512 * z^(3 / 2 : ℝ) / h^2 := by
  have hp := doubleBoxAverage_psi_error_zero_sum a h ha hh
  have hz := smoothed_zero_norm_quarter_bound a h z ha hh haz hT
  have hr : 512 * (a + 2 * h)^(3 / 2 : ℝ) / h^2 ≤
      512 * z^(3 / 2 : ℝ) / h^2 := by gcongr
  linarith

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z) (hT : 4 ≤ z / h),
    (∑' ρ : DusartSmoothing.NontrivialZetaZero,
      ‖(DusartSmoothing.RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ)
) ∧
(
    ∀ (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z) (hT : 4 ≤ z / h),
    |doubleBoxAverage Chebyshev.psi a h - (a + h)| ≤
      2 + 192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ) + 512 * z^(3 / 2 : ℝ) / h^2
) := by
  exact ⟨smoothed_zero_norm_quarter_bound, double_average_quarter_bound⟩
