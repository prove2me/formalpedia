-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.TableLargeRows
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:12:08.644822+00:00
-- url     : https://prove2.me/submissions/d65528c4-9efa-4881-8983-ea8158de316f

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ImprovedRegion

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem improved_region : ∀ (s : ℂ) (ht : 2 * Real.pi < |s.im|)
    (hσ : 1 - 1 / ((31 / 10 : ℝ) * Real.log |s.im|) < s.re),
    riemannZeta s ≠ 0 :=
  ExplicitPNT.DusartTable1.Modules.ImprovedRegion.2.2.2

private theorem scaled_decay (q u : ℝ) (hq : 1 ≤ q) (hu : q ≤ u) :
    u * Real.exp (-u) ≤ q * Real.exp (-q) := by
  have h := Real.add_one_le_exp (u - q)
  have hlinear : u ≤ q * Real.exp (u - q) := by
    calc
      u ≤ q * (u - q + 1) := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hu)]
      _ ≤ q * Real.exp (u - q) := mul_le_mul_of_nonneg_left h (by linarith)
  calc
    u * Real.exp (-u) ≤ q * Real.exp (u - q) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
    _ = q * Real.exp (-q) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

private theorem improved_envelope (q u : ℝ) (hq : 31 ≤ q) (hu : q ≤ u) :
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u) ≤
      (16 / 55 : ℝ) * q * Real.exp (-q) := by
  have hc : Real.sqrt (8 / Real.pi) ≤ (8 / 5 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · apply (div_le_iff₀ Real.pi_pos).2
      have hp := Real.pi_gt_d2
      norm_num at hp ⊢
      linarith
  have hs : Real.sqrt u ≤ (2 / 11 : ℝ) * u := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num) (by linarith)
    · nlinarith [mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ u - 121 / 4 by linarith)]
  calc
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u)
      ≤ (8 / 5 : ℝ) * ((2 / 11 : ℝ) * u) * Real.exp (-u) := by gcongr
    _ = (16 / 55 : ℝ) * (u * Real.exp (-u)) := by ring
    _ ≤ (16 / 55 : ℝ) * (q * Real.exp (-q)) :=
      mul_le_mul_of_nonneg_left (scaled_decay q u (by linarith) hu) (by norm_num)
    _ = _ := by ring

private theorem psi_from_integer_certificate
    (b : ℝ) (q : ℕ) (ε : ℝ)
    (hq : 31 ≤ q)
    (hsq : (q : ℝ)^2 * (31 / 10 : ℝ) ≤ b)
    (hε : 0 ≤ ε)
    (hnum : (16 / 55 : ℝ) * q ≤ ε * (2718281828 / 10^9 : ℝ)^q)
    (x : ℝ) (hx : Real.exp b ≤ x) :
    |Chebyshev.psi x - x| ≤ ε * x := by
  have hx0 := (Real.exp_pos b).trans_le hx
  have hlog : b ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos b) hx
    simpa only [Real.log_exp] using h
  let X : ℝ := Real.sqrt (Real.log x / (31 / 10 : ℝ))
  have hX : (q : ℝ) ≤ X := by
    apply Real.le_sqrt_of_sq_le
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 31 / 10)).2 (hsq.trans hlog)
  have hqR : (31 : ℝ) ≤ q := by exact_mod_cast hq
  have hX31 : 31 ≤ X := hqR.trans hX
  have hthreshold : max (836 / 100 : ℝ) (8 / (31 / 10 : ℝ)) < X := by
    norm_num
    linarith
  have hpsi := ExplicitPNT.dusart_refined_psi_error_of_zero_free_region
    (31 / 10 : ℝ) (by norm_num) improved_region x hx0 hthreshold
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
  have hn : (16 / 55 : ℝ) * q * Real.exp (-(q : ℝ)) ≤ ε := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).2
    exact hnum.trans (mul_le_mul_of_nonneg_left hpow hε)
  have hbound := (improved_envelope (q : ℝ) X hqR hX).trans hn
  apply hpsi.le.trans
  calc
    x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) *
        Real.sqrt (Real.sqrt (1 - (Real.log (2 * Real.pi) - 1 / 2) / X))
      ≤ x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) * 1 := by gcongr
    _ = x * (Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X)) := by ring
    _ ≤ x * ε := mul_le_mul_of_nonneg_left hbound hx0.le
    _ = _ := by ring

private theorem row_3000 (x : ℝ) (hx : Real.exp 3000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (3156 / 10^16 : ℝ) * x := by
  exact psi_from_integer_certificate 3000 31 (3156 / 10^16) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_3500 (x : ℝ) (hx : Real.exp 3500 ≤ x) :
    |Chebyshev.psi x - x| ≤ (1116 / 10^16 : ℝ) * x := by
  exact psi_from_integer_certificate 3500 33 (1116 / 10^16) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_4000 (x : ℝ) (hx : Real.exp 4000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (3946 / 10^17 : ℝ) * x := by
  exact psi_from_integer_certificate 4000 35 (3946 / 10^17) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_4500 (x : ℝ) (hx : Real.exp 4500 ≤ x) :
    |Chebyshev.psi x - x| ≤ (1274 / 10^17 : ℝ) * x := by
  exact psi_from_integer_certificate 4500 38 (1274 / 10^17) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_5000 (x : ℝ) (hx : Real.exp 5000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (3956 / 10^18 : ℝ) * x := by
  exact psi_from_integer_certificate 5000 40 (3956 / 10^18) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_6000 (x : ℝ) (hx : Real.exp 6000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (4893 / 10^19 : ℝ) * x := by
  exact psi_from_integer_certificate 6000 43 (4893 / 10^19) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_7000 (x : ℝ) (hx : Real.exp 7000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (6393 / 10^20 : ℝ) * x := by
  exact psi_from_integer_certificate 7000 47 (6393 / 10^20) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_8000 (x : ℝ) (hx : Real.exp 8000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (8969 / 10^21 : ℝ) * x := by
  exact psi_from_integer_certificate 8000 50 (8969 / 10^21) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_9000 (x : ℝ) (hx : Real.exp 9000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (2427 / 10^21 : ℝ) * x := by
  exact psi_from_integer_certificate 9000 53 (2427 / 10^21) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x hx

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (q u : ℝ) (hq : 1 ≤ q) (hu : q ≤ u),
    u * Real.exp (-u) ≤ q * Real.exp (-q)
) ∧
(
    ∀ (q u : ℝ) (hq : 31 ≤ q) (hu : q ≤ u),
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u) ≤
      (16 / 55 : ℝ) * q * Real.exp (-q)
) ∧
(
    ∀ (b : ℝ) (q : ℕ) (ε : ℝ)
    (hq : 31 ≤ q)
    (hsq : (q : ℝ)^2 * (31 / 10 : ℝ) ≤ b)
    (hε : 0 ≤ ε)
    (hnum : (16 / 55 : ℝ) * q ≤ ε * (2718281828 / 10^9 : ℝ)^q)
    (x : ℝ) (hx : Real.exp b ≤ x),
    |Chebyshev.psi x - x| ≤ ε * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 3000 ≤ x),
    |Chebyshev.psi x - x| ≤ (3156 / 10^16 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 3500 ≤ x),
    |Chebyshev.psi x - x| ≤ (1116 / 10^16 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 4000 ≤ x),
    |Chebyshev.psi x - x| ≤ (3946 / 10^17 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 4500 ≤ x),
    |Chebyshev.psi x - x| ≤ (1274 / 10^17 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 5000 ≤ x),
    |Chebyshev.psi x - x| ≤ (3956 / 10^18 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 6000 ≤ x),
    |Chebyshev.psi x - x| ≤ (4893 / 10^19 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 7000 ≤ x),
    |Chebyshev.psi x - x| ≤ (6393 / 10^20 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 8000 ≤ x),
    |Chebyshev.psi x - x| ≤ (8969 / 10^21 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 9000 ≤ x),
    |Chebyshev.psi x - x| ≤ (2427 / 10^21 : ℝ) * x
) := by
  exact ⟨scaled_decay, improved_envelope, psi_from_integer_certificate, row_3000, row_3500, row_4000, row_4500, row_5000, row_6000, row_7000, row_8000, row_9000⟩
