-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.RegionCertificates
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:24:11.832127+00:00
-- url     : https://prove2.me/submissions/39e1a705-5ab2-43ac-8b75-689697764280

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_TableLargeRows

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem region100 : ∀ (s : ℂ) (ht : 2 * Real.pi < |s.im|)
    (hσ : 1 - 1 / ((7 / 4 : ℝ) * Real.log |s.im|) < s.re),
    riemannZeta s ≠ 0 :=
  ExplicitPNT.DusartTable1.Modules.Region100.2.2

private theorem scaled_decay : ∀ (q u : ℝ) (hq : 1 ≤ q) (hu : q ≤ u),
    u * Real.exp (-u) ≤ q * Real.exp (-q) :=
  ExplicitPNT.DusartTable1.Modules.TableLargeRows.1

private theorem envelope_five (q u : ℝ) (hq : 25 ≤ q) (hu : q ≤ u) :
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u) ≤
      (8 / 25 : ℝ) * q * Real.exp (-q) := by
  have hc : Real.sqrt (8 / Real.pi) ≤ (8 / 5 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · apply (div_le_iff₀ Real.pi_pos).2
      have hp := Real.pi_gt_d2
      norm_num at hp ⊢
      linarith
  have hs : Real.sqrt u ≤ (1 / 5 : ℝ) * u := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num) (by linarith)
    · nlinarith [mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ u - 25 by linarith)]
  calc
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u)
      ≤ (8 / 5 : ℝ) * ((1 / 5 : ℝ) * u) * Real.exp (-u) := by gcongr
    _ = (8 / 25 : ℝ) * (u * Real.exp (-u)) := by ring
    _ ≤ (8 / 25 : ℝ) * (q * Real.exp (-q)) :=
      mul_le_mul_of_nonneg_left (scaled_decay q u (by linarith) hu) (by norm_num)
    _ = _ := by ring

private theorem psi_of_region_certificate
    (R b : ℝ) (q : ℕ) (ε : ℝ) (hR : (1 / 2 : ℝ) ≤ R)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (hq : 25 ≤ q) (hsq : (q : ℝ)^2 * R ≤ b) (hε : 0 ≤ ε)
    (hnum : (8 / 25 : ℝ) * q ≤ ε * (2718281828 / 10^9 : ℝ)^q)
    (x : ℝ) (hx : Real.exp b ≤ x) :
    |Chebyshev.psi x - x| ≤ ε * x := by
  have hR0 : 0 < R := by linarith
  have hx0 := (Real.exp_pos b).trans_le hx
  have hlog : b ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos b) hx
    simpa only [Real.log_exp] using h
  let X : ℝ := Real.sqrt (Real.log x / R)
  have hX : (q : ℝ) ≤ X := by
    apply Real.le_sqrt_of_sq_le
    exact (le_div_iff₀ hR0).2 (hsq.trans hlog)
  have hqR : (25 : ℝ) ≤ q := by exact_mod_cast hq
  have hX25 : 25 ≤ X := hqR.trans hX
  have h16 : (8 : ℝ) / R ≤ 16 := (div_le_iff₀ hR0).2 (by linarith)
  have hthreshold : max (836 / 100 : ℝ) (8 / R) < X := max_lt (by linarith) (by linarith)
  have hpsi := ExplicitPNT.dusart_refined_psi_error_of_zero_free_region R hR0 hzero x hx0 hthreshold
  change |Chebyshev.psi x - x| < x * Real.sqrt (8 / Real.pi) * Real.sqrt X *
    Real.exp (-X) * Real.sqrt (Real.sqrt
      (1 - (Real.log (2 * Real.pi) - 1 / 2) / X)) at hpsi
  have hf : Real.sqrt (Real.sqrt
      (1 - (Real.log (2 * Real.pi) - 1 / 2) / X)) ≤ 1 := by
    have hlogpi : (1 : ℝ) < Real.log (2 * Real.pi) := by
      apply (Real.lt_log_iff_exp_lt (by positivity)).2
      have he := Real.exp_one_lt_d9
      have hp := Real.pi_gt_three
      norm_num at he
      linarith
    apply Real.sqrt_le_one.mpr
    apply Real.sqrt_le_one.mpr
    have hd := div_nonneg (show 0 ≤ Real.log (2 * Real.pi) - 1 / 2 by linarith)
      (show 0 ≤ X by linarith)
    linarith
  have hpow : (2718281828 / 10^9 : ℝ)^q ≤ Real.exp (q : ℝ) := by
    have he : (2718281828 / 10^9 : ℝ) ≤ Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      norm_num at h ⊢
      linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718281828 / 10^9) he q
    simpa only [← Real.exp_nat_mul, mul_one] using hp
  have hn : (8 / 25 : ℝ) * q * Real.exp (-(q : ℝ)) ≤ ε := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).2
    exact hnum.trans (mul_le_mul_of_nonneg_left hpow hε)
  have hbound := (envelope_five (q : ℝ) X hqR hX).trans hn
  apply hpsi.le.trans
  calc
    x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) *
        Real.sqrt (Real.sqrt (1 - (Real.log (2 * Real.pi) - 1 / 2) / X))
      ≤ x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) * 1 := by gcongr
    _ = x * (Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X)) := by ring
    _ ≤ x * ε := mul_le_mul_of_nonneg_left hbound hx0.le
    _ = _ := by ring

private theorem row_1500 (x : ℝ) (hx : Real.exp 1500 ≤ x) :
    |Chebyshev.psi x - x| ≤ (5311 / 10^15 : ℝ) * x := by
  exact psi_of_region_certificate (7 / 4) 1500 29 (5311 / 10^15) (by norm_num)
    region100 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_2000 (x : ℝ) (hx : Real.exp 2000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (2536 / 10^15 : ℝ) * x := by
  exact psi_of_region_certificate (7 / 4) 2000 33 (2536 / 10^15) (by norm_num)
    region100 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_2500 (x : ℝ) (hx : Real.exp 2500 ≤ x) :
    |Chebyshev.psi x - x| ≤ (8941 / 10^16 : ℝ) * x := by
  exact psi_of_region_certificate (7 / 4) 2500 37 (8941 / 10^16) (by norm_num)
    region100 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (q u : ℝ) (hq : 25 ≤ q) (hu : q ≤ u),
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u) ≤
      (8 / 25 : ℝ) * q * Real.exp (-q)
) ∧
(
    ∀ (R b : ℝ) (q : ℕ) (ε : ℝ) (hR : (1 / 2 : ℝ) ≤ R)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (hq : 25 ≤ q) (hsq : (q : ℝ)^2 * R ≤ b) (hε : 0 ≤ ε)
    (hnum : (8 / 25 : ℝ) * q ≤ ε * (2718281828 / 10^9 : ℝ)^q)
    (x : ℝ) (hx : Real.exp b ≤ x),
    |Chebyshev.psi x - x| ≤ ε * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 1500 ≤ x),
    |Chebyshev.psi x - x| ≤ (5311 / 10^15 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 2000 ≤ x),
    |Chebyshev.psi x - x| ≤ (2536 / 10^15 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 2500 ≤ x),
    |Chebyshev.psi x - x| ≤ (8941 / 10^16 : ℝ) * x
) := by
  exact ⟨envelope_five, psi_of_region_certificate, row_1500, row_2000, row_2500⟩
