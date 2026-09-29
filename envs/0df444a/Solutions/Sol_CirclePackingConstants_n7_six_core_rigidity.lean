-- Prove2me | solution 1 for CirclePackingConstants.n7_six_core_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T00:40:42.911983+00:00
-- url     : https://prove2.me/submissions/dbff398c-2514-4c81-a208-f8c4581cfbde

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
noncomputable section
noncomputable section
namespace CirclePackingConstants
set_option maxHeartbeats 2000000

lemma contact_horizontal
    {s M eta x y : ℝ}
    (hs : 0 < s)
    (heta : eta = 4 * M ^ 2 / s)
    (hsep : s ^ 2 ≤ (s + x) ^ 2 + y ^ 2)
    (hbound : x ^ 2 + y ^ 2 ≤ 8 * M ^ 2) :
    x ≥ -eta := by
  have hmul : -(4 * M ^ 2) ≤ x * s := by
    nlinarith only [hsep, hbound]
  rw [heta]
  have htmp : -(4 * M ^ 2) / s ≤ x :=
    (div_le_iff₀ hs).2 (by nlinarith only [hmul])
  calc
    x ≥ -(4 * M ^ 2) / s := htmp
    _ = -(4 * M ^ 2 / s) := by ring

lemma contact_slope
    {s r M eta x y : ℝ}
    (hs : 0 < s)
    (heta : eta = 4 * M ^ 2 / s)
    (hr2 : r ^ 2 = 3)
    (hrel : 2 * (1 - s) = r * s)
    (hsep : s ^ 2 ≤ (1 - s + x) ^ 2 + (s / 2 + y) ^ 2)
    (hbound : x ^ 2 + y ^ 2 ≤ 8 * M ^ 2) :
    r * x + y ≥ -2 * eta := by
  have hrel_sq : (2 * (1 - s)) ^ 2 = (r * s) ^ 2 :=
    congrArg (fun z : ℝ => z ^ 2) hrel
  have hbase : (1 - s) ^ 2 + (s / 2) ^ 2 = s ^ 2 := by
    nlinarith only [hr2, hrel_sq]
  have hexpand : 0 ≤ 2 * (1 - s) * x + s * y + x ^ 2 + y ^ 2 := by
    nlinarith only [hsep, hbase]
  rw [hrel] at hexpand
  have hmul : -(8 * M ^ 2) ≤ s * (r * x + y) := by
    nlinarith only [hexpand, hbound]
  rw [heta]
  have htmp : -(8 * M ^ 2) / s ≤ r * x + y :=
    (div_le_iff₀ hs).2 (by nlinarith only [hmul])
  have hEq : -(8 * M ^ 2) / s = -2 * (4 * M ^ 2 / s) := by ring
  exact hEq ▸ htmp

end CirclePackingConstants
noncomputable section
namespace CirclePackingConstants
set_option maxHeartbeats 2000000

lemma n7_linear_bounds
    (r eta : ℝ)
    (a b c e f g h i j k l t : ℝ)
    (heta0 : 0 ≤ eta)
    (hr0 : 0 ≤ r)
    (hr15 : (3 : ℝ) / 2 ≤ r)
    (hr2 : r ^ 2 = 3)
    (hr18 : r ≤ (9 : ℝ) / 5)
    (hwa : 0 ≤ a) (hwb : 0 ≤ b) (hwe : 0 ≤ e) (hwh : 0 ≤ h)
    (hwf : f ≤ 0) (hwt : t ≤ 0)
    (hca : c - a ≥ -eta)
    (hib : i - b ≥ -eta)
    (hke : k - e ≥ -eta)
    (hjh : j - h ≥ -eta)
    (hfcg : r * (f - c) + (g - e) ≥ -2 * eta)
    (hfjg : r * (f - j) - (g - k) ≥ -2 * eta)
    (hlhti : (l - h) + r * (t - i) ≥ -2 * eta)
    (hljtk : -(l - j) + r * (t - k) ≥ -2 * eta) :
    (-eta ≤ c ∧ c ≤ 8 * eta) ∧
    (-eta ≤ i ∧ i ≤ 8 * eta) ∧
    (-eta ≤ j ∧ j ≤ 8 * eta) ∧
    (-eta ≤ k ∧ k ≤ 8 * eta) ∧
    (0 ≤ a ∧ a ≤ 9 * eta) ∧
    (0 ≤ b ∧ b ≤ 9 * eta) ∧
    (0 ≤ e ∧ e ≤ 9 * eta) ∧
    (0 ≤ h ∧ h ≤ 9 * eta) ∧
    (-5 * eta ≤ f ∧ f ≤ 0) ∧
    (-5 * eta ≤ t ∧ t ≤ 0) ∧
    (-4 * eta ≤ g ∧ g ≤ 12 * eta) ∧
    (-4 * eta ≤ l ∧ l ≤ 12 * eta) := by
  have hc_lo : -eta ≤ c := by linarith only [hca, hwa]
  have hi_lo : -eta ≤ i := by linarith only [hib, hwb]
  have hj_lo : -eta ≤ j := by linarith only [hjh, hwh]
  have hk_lo : -eta ≤ k := by linarith only [hke, hwe]
  have hrc_lo : -r * eta ≤ r * c := by
    have h := mul_le_mul_of_nonneg_left hc_lo hr0
    nlinarith only [h]
  have hri_lo : -r * eta ≤ r * i := by
    have h := mul_le_mul_of_nonneg_left hi_lo hr0
    nlinarith only [h]
  have hrj_lo : -r * eta ≤ r * j := by
    have h := mul_le_mul_of_nonneg_left hj_lo hr0
    nlinarith only [h]
  have hrk_lo : -r * eta ≤ r * k := by
    have h := mul_le_mul_of_nonneg_left hk_lo hr0
    nlinarith only [h]
  have hrf_nonpos : r * f ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 hwf
  have hrt_nonpos : r * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 hwt
  have hsum_sl1' : r * c + r * j + e - k ≤ 4 * eta := by
    linarith only [hfcg, hfjg, hrf_nonpos]
  have hsum_sl1 : r * (c + j) + e - k ≤ 4 * eta := by
    nlinarith only [hsum_sl1']
  have hsum_sl2' : r * i + r * k + h - j ≤ 4 * eta := by
    linarith only [hlhti, hljtk, hrt_nonpos]
  have hsum_sl2 : r * (i + k) + h - j ≤ 4 * eta := by
    nlinarith only [hsum_sl2']
  have hjk1 : r * j - k ≤ (4 + r) * eta := by
    linarith only [hsum_sl1, hrc_lo, hwe]
  have hjk2 : r * k - j ≤ (4 + r) * eta := by
    linarith only [hsum_sl2, hri_lo, hwh]
  have hr_sq_le : r ^ 2 ≤ ((9 : ℝ) / 5) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hr18) (by linarith only [hr0])
    nlinarith only [h]
  have hcoef : (r + 1) * (r + 4) ≤ 16 := by
    nlinarith only [hr2, hr18]
  have hj_raw : 2 * j ≤ (r + 1) * (r + 4) * eta := by
    have hm := mul_le_mul_of_nonneg_left hjk1 hr0
    have hpoly : (r ^ 2 - 1) * j ≤ (r + 1) * (r + 4) * eta := by
      nlinarith only [hm, hjk2]
    calc
      2 * j = (r ^ 2 - 1) * j := by rw [hr2]; ring
      _ ≤ (r + 1) * (r + 4) * eta := hpoly
  have hk_raw : 2 * k ≤ (r + 1) * (r + 4) * eta := by
    have hm := mul_le_mul_of_nonneg_left hjk2 hr0
    have hpoly : (r ^ 2 - 1) * k ≤ (r + 1) * (r + 4) * eta := by
      nlinarith only [hm, hjk1]
    calc
      2 * k = (r ^ 2 - 1) * k := by rw [hr2]; ring
      _ ≤ (r + 1) * (r + 4) * eta := hpoly
  have hcoef_eta : (r + 1) * (r + 4) * eta ≤ 16 * eta :=
    mul_le_mul_of_nonneg_right hcoef heta0
  have hj_upper : j ≤ 8 * eta := by nlinarith only [hj_raw, hcoef_eta]
  have hk_upper : k ≤ 8 * eta := by nlinarith only [hk_raw, hcoef_eta]
  have hrc_upper : r * c ≤ (12 + r) * eta := by
    nlinarith only [hsum_sl1, hrj_lo, hk_upper, hwe]
  have hri_upper : r * i ≤ (12 + r) * eta := by
    nlinarith only [hsum_sl2, hrk_lo, hj_upper, hwh]
  have hr_ge_12_7 : (12 : ℝ) / 7 ≤ r := by
    nlinarith only [hr2, hr0]
  have hcoef_c : (12 + r) * eta ≤ (8 * r) * eta := by
    have hh := mul_le_mul_of_nonneg_right hr_ge_12_7 heta0
    nlinarith only [hh]
  have hc_upper : c ≤ 8 * eta := by
    have hrpos : 0 < r := by linarith only [hr15]
    apply le_of_mul_le_mul_left _ hrpos
    nlinarith only [hrc_upper, hcoef_c]
  have hi_upper : i ≤ 8 * eta := by
    have hrpos : 0 < r := by linarith only [hr15]
    apply le_of_mul_le_mul_left _ hrpos
    nlinarith only [hri_upper, hcoef_c]
  have ha_upper : a ≤ 9 * eta := by linarith only [hca, hc_upper]
  have hb_upper : b ≤ 9 * eta := by linarith only [hib, hi_upper]
  have he_upper : e ≤ 9 * eta := by linarith only [hke, hk_upper]
  have hh_upper : h ≤ 9 * eta := by linarith only [hjh, hj_upper]
  have hpre1 : -4 * eta ≤ 2 * r * f - r * (c + j) - e + k := by
    linarith only [hfcg, hfjg]
  have hpre2 : -4 * eta ≤ 2 * r * t - r * (i + k) - h + j := by
    linarith only [hlhti, hljtk]
  have hrawf : -(12 + 2 * r) * eta ≤ 2 * r * f := by
    nlinarith only [hpre1, hrc_lo, hrj_lo, hk_upper, hwe]
  have hrawt : -(12 + 2 * r) * eta ≤ 2 * r * t := by
    nlinarith only [hpre2, hri_lo, hrk_lo, hj_upper, hwh]
  have hf_lower : -5 * eta ≤ f := by
    have hrpos : 0 < r := by linarith only [hr15]
    have hcoef_f : -(10 * r) * eta ≤ -(12 + 2 * r) * eta := by
      nlinarith only [hr15, heta0]
    have hmul : -(10 * r) * eta ≤ 2 * r * f := le_trans hcoef_f hrawf
    apply le_of_mul_le_mul_left _ (by linarith only [hr15] : 0 < 2 * r)
    nlinarith only [hmul]
  have ht_lower : -5 * eta ≤ t := by
    have hcoef_t : -(10 * r) * eta ≤ -(12 + 2 * r) * eta := by
      nlinarith only [hr15, heta0]
    have hmul : -(10 * r) * eta ≤ 2 * r * t := le_trans hcoef_t hrawt
    apply le_of_mul_le_mul_left _ (by linarith only [hr15] : 0 < 2 * r)
    nlinarith only [hmul]
  have hg_lower : -(2 + r) * eta ≤ g := by
    nlinarith only [hfcg, hrc_lo, hrf_nonpos, hwe]
  have h_rfj_upper : r * (f - j) ≤ r * eta := by
    nlinarith only [hrf_nonpos, hrj_lo]
  have hg_upper : g ≤ (10 + r) * eta := by
    nlinarith only [hfjg, h_rfj_upper, hk_upper]
  have hl_lower : -(2 + r) * eta ≤ l := by
    nlinarith only [hlhti, hri_lo, hrt_nonpos, hwh]
  have h_rtk_upper : r * (t - k) ≤ r * eta := by
    nlinarith only [hrt_nonpos, hrk_lo]
  have hl_upper : l ≤ (10 + r) * eta := by
    nlinarith only [hljtk, h_rtk_upper, hj_upper]
  have hr_le_two : r ≤ 2 := by nlinarith only [hr18]
  have hg_lo4 : -4 * eta ≤ g := by
    nlinarith only [hg_lower, hr_le_two, heta0]
  have hg_hi12 : g ≤ 12 * eta := by
    nlinarith only [hg_upper, hr_le_two, heta0]
  have hl_lo4 : -4 * eta ≤ l := by
    nlinarith only [hl_lower, hr_le_two, heta0]
  have hl_hi12 : l ≤ 12 * eta := by
    nlinarith only [hl_upper, hr_le_two, heta0]
  exact ⟨⟨hc_lo, hc_upper⟩, ⟨hi_lo, hi_upper⟩,
    ⟨hj_lo, hj_upper⟩, ⟨hk_lo, hk_upper⟩,
    ⟨hwa, ha_upper⟩, ⟨hwb, hb_upper⟩, ⟨hwe, he_upper⟩,
    ⟨hwh, hh_upper⟩, ⟨hf_lower, hwf⟩, ⟨ht_lower, hwt⟩,
    ⟨hg_lo4, hg_hi12⟩, ⟨hl_lo4, hl_hi12⟩⟩

end CirclePackingConstants
namespace CirclePackingConstants

private lemma diff_sq_le_rig {M x y : ℝ}
    (hxL : -M ≤ x) (hxU : x ≤ M)
    (hyL : -M ≤ y) (hyU : y ≤ M) :
    (x - y) ^ 2 ≤ (2 * M) ^ 2 := by
  have h1 : -(2 * M) ≤ x - y := by linarith
  have h2 : x - y ≤ 2 * M := by linarith
  have hb : 0 ≤ 2 * M := by linarith
  exact (by
    have hleft : 0 ≤ 2 * M - (x-y) := by linarith
    have hright : 0 ≤ 2 * M + (x-y) := by linarith
    nlinarith only [mul_nonneg hleft hright])

private lemma diff_sum_sq_le_rig {M x1 y1 x2 y2 : ℝ}
    (hx1L : -M ≤ x1) (hx1U : x1 ≤ M)
    (hy1L : -M ≤ y1) (hy1U : y1 ≤ M)
    (hx2L : -M ≤ x2) (hx2U : x2 ≤ M)
    (hy2L : -M ≤ y2) (hy2U : y2 ≤ M) :
    (x1 - x2) ^ 2 + (y1 - y2) ^ 2 ≤ 8 * M ^ 2 := by
  have hx := diff_sq_le_rig hx1L hx1U hx2L hx2U
  have hy := diff_sq_le_rig hy1L hy1U hy2L hy2U
  nlinarith only [hx, hy]

end CirclePackingConstants

open CirclePackingConstants

theorem solution
    (s r M eta : ℝ)
    (a b c e f g h i j k l t : ℝ)
    (hs : 0 < s)
    (hs_half : (1 : ℝ) / 2 < s)
    (hr0 : 0 ≤ r)
    (hr15 : (3 : ℝ) / 2 ≤ r)
    (hr18 : r ≤ (9 : ℝ) / 5)
    (hr2 : r ^ 2 = 3)
    (hrel : 2 * (1 - s) = r * s)
    (hM0 : 0 ≤ M)
    (hMsmall : M ≤ (1 : ℝ) / 100)
    (heta : eta = 4 * M ^ 2 / s)
    (hmax : M = max (|a|) (max (|b|) (max (|c|) (max (|e|) (max (|f|) (max (|g|)
      (max (|h|) (max (|i|) (max (|j|) (max (|k|) (max (|l|) (|t|))))))))))))
    (haL : -M ≤ a) (haU : a ≤ M)
    (hbL : -M ≤ b) (hbU : b ≤ M)
    (hcL : -M ≤ c) (hcU : c ≤ M)
    (heL : -M ≤ e) (heU : e ≤ M)
    (hfL : -M ≤ f) (hfU : f ≤ M)
    (hgL : -M ≤ g) (hgU : g ≤ M)
    (hhL : -M ≤ h) (hhU : h ≤ M)
    (hiL : -M ≤ i) (hiU : i ≤ M)
    (hjL : -M ≤ j) (hjU : j ≤ M)
    (hkL : -M ≤ k) (hkU : k ≤ M)
    (hlL : -M ≤ l) (hlU : l ≤ M)
    (htL : -M ≤ t) (htU : t ≤ M)
    (hwa : 0 ≤ a) (hwb : 0 ≤ b) (hwe : 0 ≤ e) (hwh : 0 ≤ h)
    (hwf : f ≤ 0) (hwt : t ≤ 0)
    (C1 : s ^ 2 ≤ (s + c - a) ^ 2 + (e - b) ^ 2)
    (C2 : s ^ 2 ≤ (h - a) ^ 2 + (s + i - b) ^ 2)
    (C3 : s ^ 2 ≤ (j - c) ^ 2 + (s + k - e) ^ 2)
    (C4 : s ^ 2 ≤ (s + j - h) ^ 2 + (k - i) ^ 2)
    (C5 : s ^ 2 ≤ (1 - s + f - c) ^ 2 + (s / 2 + g - e) ^ 2)
    (C6 : s ^ 2 ≤ (1 - s + f - j) ^ 2 + (-s / 2 + g - k) ^ 2)
    (C7 : s ^ 2 ≤ (s / 2 + l - h) ^ 2 + (1 - s + t - i) ^ 2)
    (C8 : s ^ 2 ≤ (-s / 2 + l - j) ^ 2 + (1 - s + t - k) ^ 2) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧
      h = 0 ∧ i = 0 ∧ j = 0 ∧ k = 0 ∧ l = 0 ∧ t = 0 := by
  have hsum1 := diff_sum_sq_le_rig hcL hcU heL heU haL haU hbL hbU
  have hsum2 := diff_sum_sq_le_rig hhL hhU hiL hiU haL haU hbL hbU
  have hsum3 := diff_sum_sq_le_rig hjL hjU hkL hkU hcL hcU heL heU
  have hsum4 := diff_sum_sq_le_rig hjL hjU hkL hkU hhL hhU hiL hiU
  have hsum5 := diff_sum_sq_le_rig hfL hfU hgL hgU hcL hcU heL heU
  have hsum6 := diff_sum_sq_le_rig hfL hfU hgL hgU hjL hjU hkL hkU
  have hsum7 := diff_sum_sq_le_rig hlL hlU htL htU hhL hhU hiL hiU
  have hsum8 := diff_sum_sq_le_rig hlL hlU htL htU hjL hjU hkL hkU
  have hC1' : s ^ 2 ≤ (s + (c-a)) ^ 2 + (e-b) ^ 2 := by
    nlinarith only [C1]
  have hC2' : s ^ 2 ≤ (s + (i-b)) ^ 2 + (h-a) ^ 2 := by
    nlinarith only [C2]
  have hC3' : s ^ 2 ≤ (s + (k-e)) ^ 2 + (j-c) ^ 2 := by
    nlinarith only [C3]
  have hC4' : s ^ 2 ≤ (s + (j-h)) ^ 2 + (k-i) ^ 2 := by
    nlinarith only [C4]
  have hca : c - a ≥ -eta := contact_horizontal hs heta hC1' (by nlinarith only [hsum1])
  have hib : i - b ≥ -eta := contact_horizontal hs heta hC2' (by nlinarith only [hsum2])
  have hke : k - e ≥ -eta := contact_horizontal hs heta hC3' (by nlinarith only [hsum3])
  have hjh : j - h ≥ -eta := contact_horizontal hs heta hC4' (by nlinarith only [hsum4])
  have hfcg : r * (f-c) + (g-e) ≥ -2*eta := by
    apply contact_slope hs heta hr2 hrel
    · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using C5
    · exact hsum5
  have hfjg : r * (f-j) - (g-k) ≥ -2*eta := by
    have hC6' : s ^ 2 ≤ (1-s + (f-j)) ^ 2 + (s/2 + (-(g-k))) ^ 2 := by
      convert C6 using 1 <;> ring
    have hsum6' : (f-j)^2 + (-(g-k))^2 ≤ 8*M^2 := by
      nlinarith only [hsum6]
    have h := contact_slope hs heta hr2 hrel hC6' hsum6'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hlhti : (l-h) + r*(t-i) ≥ -2*eta := by
    have hC7' : s ^ 2 ≤ (1-s + (t-i)) ^ 2 + (s/2 + (l-h)) ^ 2 := by
      nlinarith only [C7]
    have hsum7' : (t-i)^2 + (l-h)^2 ≤ 8*M^2 := by
      nlinarith only [hsum7]
    have h := contact_slope hs heta hr2 hrel hC7' hsum7'
    nlinarith only [h]
  have hljtk : -(l-j) + r*(t-k) ≥ -2*eta := by
    have hC8' : s ^ 2 ≤ (1-s + (t-k)) ^ 2 + (s/2 + (-(l-j))) ^ 2 := by
      convert C8 using 1 <;> ring
    have hsum8' : (t-k)^2 + (-(l-j))^2 ≤ 8*M^2 := by
      nlinarith only [hsum8]
    have h := contact_slope hs heta hr2 hrel hC8' hsum8'
    nlinarith only [h]
  have hlin := n7_linear_bounds r eta a b c e f g h i j k l t
    (by rw [heta]; positivity) hr0 hr15 hr2 hr18
    hwa hwb hwe hwh hwf hwt hca hib hke hjh hfcg hfjg hlhti hljtk
  rcases hlin with ⟨hcB, hiB, hjB, hkB, haB, hbB, heB, hhB,
    hfB, htB, hgB, hlB⟩
  have h_abs_a : |a| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [haB.1], by linarith [haB.2]⟩
  have h_abs_b : |b| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [hbB.1], by linarith [hbB.2]⟩
  have h_abs_c : |c| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [hcB.1], by linarith [hcB.2]⟩
  have h_abs_e : |e| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [heB.1], by linarith [heB.2]⟩
  have h_abs_f : |f| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [hfB.1], by linarith [hfB.2]⟩
  have h_abs_g : |g| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [hgB.1], by linarith [hgB.2]⟩
  have h_abs_h : |h| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [hhB.1], by linarith [hhB.2]⟩
  have h_abs_i : |i| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [hiB.1], by linarith [hiB.2]⟩
  have h_abs_j : |j| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [hjB.1], by linarith [hjB.2]⟩
  have h_abs_k : |k| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [hkB.1], by linarith [hkB.2]⟩
  have h_abs_l : |l| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [hlB.1], by linarith [hlB.2]⟩
  have h_abs_t : |t| ≤ 12 * eta := by rw [abs_le]; exact ⟨by linarith [htB.1], by linarith [htB.2]⟩
  have hM_upper : M ≤ 12 * eta := by
    rw [hmax]
    apply max_le
    · exact h_abs_a
    apply max_le
    · exact h_abs_b
    apply max_le
    · exact h_abs_c
    apply max_le
    · exact h_abs_e
    apply max_le
    · exact h_abs_f
    apply max_le
    · exact h_abs_g
    apply max_le
    · exact h_abs_h
    apply max_le
    · exact h_abs_i
    apply max_le
    · exact h_abs_j
    apply max_le
    · exact h_abs_k
    apply max_le
    · exact h_abs_l
    · exact h_abs_t
  have hM_eta : s * M ≤ 48 * M ^ 2 := by
    rw [heta] at hM_upper
    have hsne : s ≠ 0 := ne_of_gt hs
    field_simp [hsne] at hM_upper
    nlinarith only [hM_upper]
  have hM_zero : M = 0 := by
    by_contra hne
    have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hne)
    have hquad : 48 * M ^ 2 ≤ (12 : ℝ) / 25 * M := by
      nlinarith only [hMsmall, hM0]
    have hsM0 := mul_lt_mul_of_pos_right hs_half hMpos
    have hsM : M / 2 < s * M := by nlinarith only [hsM0]
    nlinarith only [hM_eta, hquad, hsM]
  have hz (x : ℝ) (hx : -M ≤ x) (hx' : x ≤ M) : x = 0 := by
    have habs : |x| ≤ M := (abs_le).2 ⟨hx, hx'⟩
    have : |x| = 0 := le_antisymm (by simpa [hM_zero] using habs) (abs_nonneg x)
    exact abs_eq_zero.mp this
  exact ⟨hz a haL haU, hz b hbL hbU, hz c hcL hcU, hz e heL heU,
    hz f hfL hfU, hz g hgL hgU, hz h hhL hhU, hz i hiL hiU,
    hz j hjL hjU, hz k hkL hkU, hz l hlL hlU, hz t htL htU⟩

