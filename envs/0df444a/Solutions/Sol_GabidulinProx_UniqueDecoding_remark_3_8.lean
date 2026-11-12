-- Prove2me | solution 1 for GabidulinProx.UniqueDecoding.remark_3_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:41:33.36054+00:00
-- url     : https://prove2.me/submissions/6f95d8be-9723-4d6e-b4e6-1d3ef1a26692

import Mathlib
import Definitions.Def_GabidulinProx_UniqueDecoding_Codes

section
set_option autoImplicit false

namespace GabidulinProx.Dev.Remark38

open GabidulinProx.UniqueDecoding

lemma sigma_mul (q i : ℕ) : (sigma q i : ℝ) * ((q : ℝ) - 1) = (q : ℝ) ^ (i + 1) - 1 := by
  induction i with
  | zero => simp [sigma]
  | succ i ih =>
    have : (sigma q (i + 1) : ℝ) = sigma q i + (q : ℝ) ^ (i + 1) := by
      simp [sigma, Finset.sum_range_succ]
    rw [this, add_mul, ih]; ring

lemma sigma_pos (q i : ℕ) (hq : 1 ≤ q) : 1 ≤ sigma q i := by
  unfold sigma
  rw [Finset.sum_range_succ']
  have : 0 < ∑ x ∈ Finset.range i, q ^ (x + 1) + q ^ 0 := by simp
  omega

lemma sigma_le (q i : ℕ) (hq : 2 ≤ q) :
    (sigma q i : ℝ) ≤ (q : ℝ) / ((q : ℝ) - 1) * (q : ℝ) ^ i := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < (q : ℝ) - 1 := by linarith
  rw [show (q : ℝ) / ((q : ℝ) - 1) * (q : ℝ) ^ i = (q : ℝ) ^ (i + 1) / ((q : ℝ) - 1) by
    field_simp; ring]
  rw [le_div_iff₀ hpos, sigma_mul]; linarith

lemma tau_cast (q k e : ℕ) (hq : 2 ≤ q) :
    (tau q k e : ℝ) = (sigma q e : ℝ) * (sigma q e - 1) * sigma q (k - 1) + 2 * sigma q e - 1 := by
  have h1 := sigma_pos q e (by omega)
  have h2 := sigma_pos q (k - 1) (by omega)
  unfold tau
  obtain ⟨s, hs⟩ : ∃ s, sigma q e = s + 1 := ⟨sigma q e - 1, by omega⟩
  rw [hs]
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

end GabidulinProx.Dev.Remark38

namespace GabidulinProx.UniqueDecoding

open GabidulinProx.Dev.Remark38

theorem chk_remark_3_8 (q n k e : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (hkn : k ≤ n)
    (he : 1 ≤ e) (hdec : 2 * e < n - k + 1) :
    let r : ℝ := (q : ℝ) / ((q : ℝ) - 1)
    (tau q k e : ℝ) ≤ r ^ 3 * (q : ℝ) ^ (k + 2 * e - 1) + 2 * r * (q : ℝ) ^ e ∧
    (tau q k e : ℝ) ≤ r ^ 3 * (q : ℝ) ^ (n - 1) + 2 * r * (q : ℝ) ^ (n - 2) ∧
    r ^ 3 * (q : ℝ) ^ (n - 1) + 2 * r * (q : ℝ) ^ (n - 2) =
      (r ^ 3 + 2 / ((q : ℝ) - 1)) * (q : ℝ) ^ (n - 1) ∧
    (r ^ 3 + 2 / ((q : ℝ) - 1)) * (q : ℝ) ^ (n - 1) ≤ 10 * (q : ℝ) ^ (n - 1) ∧
    tau q k e ≤ 10 * q ^ (n - 1) ∧
    ∀ s : ℕ, 10 * q ^ (n - 1) < s → tau q k e < s := by
  intro r
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < (q : ℝ) - 1 := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hr0 : 0 ≤ r := div_nonneg hqpos.le hpos.le
  have hrle : r ≤ 2 := by
    show (q : ℝ) / ((q : ℝ) - 1) ≤ 2
    rw [div_le_iff₀ hpos]; linarith
  have hr1 : 1 ≤ r := by
    show 1 ≤ (q : ℝ) / ((q : ℝ) - 1)
    rw [le_div_iff₀ hpos]; linarith
  have hnk : k + 2 * e ≤ n := by omega
  have hen : e + 2 ≤ n := by omega
  have hs := sigma_le q e hq
  have hm := sigma_le q (k - 1) hq
  have hs1 : (1 : ℝ) ≤ sigma q e := by exact_mod_cast sigma_pos q e (by omega)
  have hm1 : (1 : ℝ) ≤ sigma q (k - 1) := by exact_mod_cast sigma_pos q (k - 1) (by omega)
  have hqe : (0 : ℝ) ≤ (q : ℝ) ^ e := by positivity
  have hqk : (0 : ℝ) ≤ (q : ℝ) ^ (k - 1) := by positivity
  -- part 1
  have h1 : (tau q k e : ℝ) ≤ r ^ 3 * (q : ℝ) ^ (k + 2 * e - 1) + 2 * r * (q : ℝ) ^ e := by
    rw [tau_cast q k e hq]
    have hexp : (q : ℝ) ^ (k + 2 * e - 1) = (q : ℝ) ^ e * (q : ℝ) ^ e * (q : ℝ) ^ (k - 1) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [hexp]
    have hss : (sigma q e : ℝ) * (sigma q e - 1) * sigma q (k - 1) ≤
        (r * (q : ℝ) ^ e) * (r * (q : ℝ) ^ e) * (r * (q : ℝ) ^ (k - 1)) := by
      have a1 : (sigma q e : ℝ) * (sigma q e - 1) ≤ (r * (q : ℝ) ^ e) * (r * (q : ℝ) ^ e) := by
        apply mul_le_mul hs (by linarith) (by linarith) (by positivity)
      calc _ ≤ ((r * (q : ℝ) ^ e) * (r * (q : ℝ) ^ e)) * sigma q (k - 1) :=
            mul_le_mul_of_nonneg_right a1 (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
    nlinarith
  have h2 : (tau q k e : ℝ) ≤ r ^ 3 * (q : ℝ) ^ (n - 1) + 2 * r * (q : ℝ) ^ (n - 2) := by
    refine h1.trans ?_
    have e1 : (q : ℝ) ^ (k + 2 * e - 1) ≤ (q : ℝ) ^ (n - 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have e2 : (q : ℝ) ^ e ≤ (q : ℝ) ^ (n - 2) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have : 0 ≤ r ^ 3 := by positivity
    nlinarith
  have h3 : r ^ 3 * (q : ℝ) ^ (n - 1) + 2 * r * (q : ℝ) ^ (n - 2) =
      (r ^ 3 + 2 / ((q : ℝ) - 1)) * (q : ℝ) ^ (n - 1) := by
    have : (q : ℝ) ^ (n - 1) = (q : ℝ) ^ (n - 2) * q := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    show _ = _
    simp only [r]
    field_simp
  have h4 : (r ^ 3 + 2 / ((q : ℝ) - 1)) * (q : ℝ) ^ (n - 1) ≤ 10 * (q : ℝ) ^ (n - 1) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have a : r ^ 3 ≤ 8 := by
      calc r ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hr0 hrle 3
        _ = 8 := by norm_num
    have b : 2 / ((q : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ hpos]; linarith
    linarith
  have h5r : (tau q k e : ℝ) ≤ 10 * (q : ℝ) ^ (n - 1) := h2.trans (h3 ▸ h4)
  have h5 : tau q k e ≤ 10 * q ^ (n - 1) := by exact_mod_cast h5r
  exact ⟨h1, h2, h3, h4, h5, fun s hs' => lt_of_le_of_lt h5 hs'⟩

end GabidulinProx.UniqueDecoding
end

theorem solution : type_of% @GabidulinProx.UniqueDecoding.chk_remark_3_8 := @GabidulinProx.UniqueDecoding.chk_remark_3_8
