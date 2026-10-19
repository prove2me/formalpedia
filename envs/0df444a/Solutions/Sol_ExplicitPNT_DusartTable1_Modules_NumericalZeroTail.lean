-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.NumericalZeroTail
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:32:54.498427+00:00
-- url     : https://prove2.me/submissions/3dd9dad3-5a2e-4db1-9db3-d2a2848d903d

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_LogarithmicZeroTail

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem finite_positive_inverse_cube_tail_log : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 1000 ≤ T) (hγ : ∀ ρ ∈ Z, T ≤ ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      ((3 / 10 : ℝ) * Real.log T + 3 / 20) / T^2 :=
  ExplicitPNT.DusartTable1.Modules.LogarithmicZeroTail.2

private theorem log_le_integer_of_certificate (T : ℝ) (n : ℕ) (hT : 0 < T)
    (hnum : T ≤ (2718281828 / 10^9 : ℝ)^n) : Real.log T ≤ (n : ℝ) := by
  apply (Real.log_le_iff_le_exp hT).2
  have he : (2718281828 / 10^9 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.exp_one_gt_d9
    norm_num at hh ⊢
    linarith
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718281828 / 10^9) he n
  rw [← Real.exp_nat_mul] at hh
  simpa only [mul_one] using hnum.trans hh

private theorem positive_inverse_cube_tsum_log (T : ℝ) (hT : 1000 ≤ T) :
    (∑' ρ : HighPositiveZero T,
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      ((3 / 10 : ℝ) * Real.log T + 3 / 20) / T^2 := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro ρ
    have hi : 0 < ρ.val.im := by linarith [ρ.property.2]
    positivity
  · intro S
    let Z : Finset ℂ := S.image (fun ρ : HighPositiveZero T => ρ.val)
    have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact ⟨τ.property.1, by linarith [τ.property.2]⟩
    have hγ : ∀ ρ ∈ Z, T ≤ ρ.im := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.2
    have hh := finite_positive_inverse_cube_tail_log Z hZ T hT hγ
    dsimp [Z] at hh
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hh
    exact hh

private theorem positive_inverse_cube_tail_at_T0 :
    (∑' ρ : HighPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (34 / 10^13 : ℝ) := by
  have hh := positive_inverse_cube_tsum_log (566245491 / 500) (by norm_num)
  have hl := log_le_integer_of_certificate (566245491 / 500) 14 (by norm_num) (by norm_num)
  apply hh.trans
  calc
    _ ≤ ((3 / 10 : ℝ) * 14 + 3 / 20) / (566245491 / 500 : ℝ)^2 := by
      gcongr
      norm_num at hl
      exact hl
    _ ≤ (34 / 10^13 : ℝ) := by norm_num

private theorem positive_inverse_cube_tail_at_H :
    (∑' ρ : HighPositiveZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (15 / 10^25 : ℝ) := by
  have hh := positive_inverse_cube_tsum_log 2445999556030 (by norm_num)
  have hl := log_le_integer_of_certificate 2445999556030 29 (by norm_num) (by norm_num)
  apply hh.trans
  calc
    _ ≤ ((3 / 10 : ℝ) * 29 + 3 / 20) / (2445999556030 : ℝ)^2 := by
      gcongr
      norm_num at hl
      exact hl
    _ ≤ (15 / 10^25 : ℝ) := by norm_num

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (T : ℝ) (n : ℕ) (hT : 0 < T)
    (hnum : T ≤ (2718281828 / 10^9 : ℝ)^n),
    Real.log T ≤ (n : ℝ)
) ∧
(
    ∀ (T : ℝ) (hT : 1000 ≤ T),
    (∑' ρ : HighPositiveZero T,
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      ((3 / 10 : ℝ) * Real.log T + 3 / 20) / T^2
) ∧
(
    (∑' ρ : HighPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (34 / 10^13 : ℝ)
) ∧
(
    (∑' ρ : HighPositiveZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (15 / 10^25 : ℝ)
) := by
  exact ⟨log_le_integer_of_certificate, positive_inverse_cube_tsum_log, positive_inverse_cube_tail_at_T0, positive_inverse_cube_tail_at_H⟩
