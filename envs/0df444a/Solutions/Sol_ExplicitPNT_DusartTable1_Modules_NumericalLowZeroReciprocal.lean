-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.NumericalLowZeroReciprocal
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:34:25.368967+00:00
-- url     : https://prove2.me/submissions/475fb702-f56e-426e-929a-8ed615247788

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_RationalLogCertificates
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_LowZeroReciprocal

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem log_le_rational_of_certificate : ∀ (x : ℝ) (m n : ℕ)
    (hx : 0 < x) (hn : 0 < n)
    (hnum : x^n ≤ (2718281828 / 10^9 : ℝ)^m),
    Real.log x ≤ (m : ℝ) / n :=
  ExplicitPNT.DusartTable1.Modules.RationalLogCertificates.1

private theorem log_fourteen_upper : Real.log (14 : ℝ) ≤ 53 / 20 :=
  ExplicitPNT.DusartTable1.Modules.RationalLogCertificates.2.2.1

private theorem finite_positive_reciprocal_log_bound : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 14 ≤ T) (hγ : ∀ ρ ∈ Z, ρ.im ≤ T),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤
      (Real.log (T / (2 * Real.pi)))^2 / (4 * Real.pi) - 1 / (4 * Real.pi) +
        (9 * Real.log 14 + 91) / 14 :=
  ExplicitPNT.DusartTable1.Modules.LowZeroReciprocal

private theorem log_T0_over_two_pi_upper :
    Real.log ((566245491 / 500 : ℝ) / (2 * Real.pi)) ≤ 61 / 5 := by
  have hr : (566245491 / 500 : ℝ) / (2 * Real.pi) ≤ (566245491 / 500 : ℝ) / 6 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith [Real.pi_gt_three]
  have hp := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ (566245491 / 500 : ℝ) / (2 * Real.pi)) hr 5
  have hn : ((566245491 / 500 : ℝ) / 6)^5 ≤ (2718281828 / 10^9 : ℝ)^61 := by
    norm_num
  simpa using log_le_rational_of_certificate
    ((566245491 / 500 : ℝ) / (2 * Real.pi)) 61 5
    (by positivity) (by norm_num) (hp.trans hn)

private theorem finite_positive_reciprocal_T0 (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, ρ.im ≤ (566245491 / 500 : ℝ)) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤ 20 := by
  have hh := finite_positive_reciprocal_log_bound Z hZ (566245491 / 500) (by norm_num) hγ
  have hl0 : 0 ≤ Real.log ((566245491 / 500 : ℝ) / (2 * Real.pi)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by positivity)).2
    linarith [Real.pi_lt_four]
  have hsq := pow_le_pow_left₀ hl0 log_T0_over_two_pi_upper 2
  have hlogterm : (Real.log ((566245491 / 500 : ℝ) / (2 * Real.pi)))^2 /
      (4 * Real.pi) ≤ (61 / 5 : ℝ)^2 / (4 * (157 / 50 : ℝ)) := by
    calc
      _ ≤ (61 / 5 : ℝ)^2 / (4 * Real.pi) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (by linarith [Real.pi_gt_d2])
  have hinv : (1 / 16 : ℝ) ≤ 1 / (4 * Real.pi) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by linarith [Real.pi_lt_four])
  have hsmall : (9 * Real.log 14 + 91) / 14 ≤ (9 * (53 / 20 : ℝ) + 91) / 14 := by
    gcongr
    exact log_fourteen_upper
  linarith only [hh, hlogterm, hinv, hsmall]

private theorem positive_reciprocal_T0 :
    (∑' ρ : LowPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im)) ≤ 20 := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro ρ
    have hi := ρ.property.2.1
    positivity
  · intro S
    let Z : Finset ℂ := S.image (fun ρ : LowPositiveZero (566245491 / 500 : ℝ) => ρ.val)
    have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact ⟨τ.property.1, τ.property.2.1⟩
    have hγ : ∀ ρ ∈ Z, ρ.im ≤ (566245491 / 500 : ℝ) := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.2.2
    have hh := finite_positive_reciprocal_T0 Z hZ hγ
    dsimp [Z] at hh
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hh
    exact hh

end ExplicitPNT.DusartTable1

theorem solution :
(
    Real.log ((566245491 / 500 : ℝ) / (2 * Real.pi)) ≤ 61 / 5
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, ρ.im ≤ (566245491 / 500 : ℝ)),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤ 20
) ∧
(
    (∑' ρ : LowPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im)) ≤ 20
) := by
  exact ⟨log_T0_over_two_pi_upper, finite_positive_reciprocal_T0, positive_reciprocal_T0⟩
