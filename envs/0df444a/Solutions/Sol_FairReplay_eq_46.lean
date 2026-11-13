-- Prove2me | solution 1 for FairReplay.eq_46
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T15:09:22.654254+00:00
-- url     : https://prove2.me/submissions/e83eeda2-2d2f-4fd8-ab13-ada973e1354d

import Mathlib

set_option autoImplicit false

/-- `K_vertex = (d²/2)(1/s + 1/r) + O(d³)`: second-order Taylor expansion of the two logarithms,
with the cubic remainder estimated by `Real.abs_log_sub_add_sum_range_le`. -/
theorem solution (p s : ℝ) (hp : 0 < p) (hs : 0 < s) (hps : p + s < 1) :
    ∃ C d₀ : ℝ, 0 < C ∧ 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d < d₀ →
      |s * Real.log (s / (s + d)) + (1 - p - s) * Real.log ((1 - p - s) / ((1 - p - s) - d)) -
          d ^ 2 / 2 * (1 / s + 1 / (1 - p - s))| ≤ C * d ^ 3 := by
  have hr : 0 < 1 - p - s := by linarith
  set r : ℝ := 1 - p - s with hrdef
  refine ⟨2 / s ^ 2 + 2 / r ^ 2, min (s / 2) (r / 2), by positivity, by positivity, ?_⟩
  intro d hd0 hdlt
  have hds : d < s / 2 := lt_of_lt_of_le hdlt (min_le_left _ _)
  have hdr : d < r / 2 := lt_of_lt_of_le hdlt (min_le_right _ _)
  set u : ℝ := d / s with hu
  set t : ℝ := d / r with ht
  have hu0 : 0 < u := div_pos hd0 hs
  have ht0 : 0 < t := div_pos hd0 hr
  have hu1 : u < 1 / 2 := by rw [hu, div_lt_iff₀ hs]; linarith
  have ht1 : t < 1 / 2 := by rw [ht, div_lt_iff₀ hr]; linarith
  have hu1' : u < 1 := by linarith
  have ht1' : t < 1 := by linarith
  have hratio_s : s / (s + d) = (1 + u)⁻¹ := by
    rw [hu]
    field_simp
  have hratio_r : r / (r - d) = (1 - t)⁻¹ := by
    rw [ht]
    field_simp
  have hlog_s : Real.log (s / (s + d)) = -Real.log (1 + u) := by
    rw [hratio_s, Real.log_inv]
  have hlog_r : Real.log (r / (r - d)) = -Real.log (1 - t) := by
    rw [hratio_r, Real.log_inv]
  have hbound_t : |t + t ^ 2 / 2 + Real.log (1 - t)| ≤ t ^ 3 / (1 - t) := by
    have h := Real.abs_log_sub_add_sum_range_le (x := t) (n := 2) (by
      rw [abs_of_nonneg ht0.le]
      exact ht1')
    rw [abs_of_nonneg ht0.le] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num at h
    convert h using 2 <;> ring
  have hbound_u : |Real.log (1 + u) - u + u ^ 2 / 2| ≤ u ^ 3 / (1 - u) := by
    have h := Real.abs_log_sub_add_sum_range_le (x := -u) (n := 2) (by
      rw [abs_neg, abs_of_nonneg hu0.le]
      exact hu1')
    rw [abs_neg, abs_of_nonneg hu0.le] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
    norm_num at h
    convert h using 2 <;> ring
  have ht_div : t ^ 3 / (1 - t) ≤ 2 * t ^ 3 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - t)]
    have hpos : 0 < t ^ 3 := pow_pos ht0 3
    have h2 : 0 < 1 - 2 * t := by linarith
    have hmul : 0 < t ^ 3 * (1 - 2 * t) := mul_pos hpos h2
    nlinarith [hmul]
  have hu_div : u ^ 3 / (1 - u) ≤ 2 * u ^ 3 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - u)]
    have hpos : 0 < u ^ 3 := pow_pos hu0 3
    have h2 : 0 < 1 - 2 * u := by linarith
    have hmul : 0 < u ^ 3 * (1 - 2 * u) := mul_pos hpos h2
    nlinarith [hmul]
  set Ru : ℝ := Real.log (1 + u) - u + u ^ 2 / 2 with hRu
  set Rt : ℝ := Real.log (1 - t) + t + t ^ 2 / 2 with hRt
  have hRu_b : |Ru| ≤ 2 * u ^ 3 := by
    rw [hRu]
    exact le_trans hbound_u hu_div
  have hRt_b : |Rt| ≤ 2 * t ^ 3 := by
    rw [show Rt = t + t ^ 2 / 2 + Real.log (1 - t) by rw [hRt]; ring]
    exact le_trans hbound_t ht_div
  have hE : s * Real.log (s / (s + d)) + r * Real.log (r / (r - d)) -
      d ^ 2 / 2 * (1 / s + 1 / r) = -(s * Ru + r * Rt) := by
    rw [hlog_s, hlog_r, hRu, hRt]
    rw [hu, ht]
    field_simp
    ring
  have hEabs : |s * Real.log (s / (s + d)) + r * Real.log (r / (r - d)) -
      d ^ 2 / 2 * (1 / s + 1 / r)| = |s * Ru + r * Rt| := by
    rw [hE, abs_neg]
  rw [hEabs]
  calc |s * Ru + r * Rt|
      ≤ |s * Ru| + |r * Rt| := abs_add_le _ _
    _ = s * |Ru| + r * |Rt| := by
        rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hr]
    _ ≤ s * (2 * u ^ 3) + r * (2 * t ^ 3) := by
        gcongr
    _ = (2 / s ^ 2 + 2 / r ^ 2) * d ^ 3 := by
        rw [hu, ht]
        field_simp
