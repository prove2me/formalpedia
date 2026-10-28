-- Prove2me | solution 1 for EthierKurtz.legendre_transform_third_order_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:42:28.556665+00:00
-- url     : https://prove2.me/submissions/f95ef7cb-12c9-4cbb-a332-bc5f9957c305

import Mathlib.Tactic
import Mathlib



theorem solution :
    ∀ (L L1 L2 : ℝ → ℝ) {t t' B R : ℝ},
      (1 / 2 : ℝ) ≤ L2 t →
        |t' - t| ≤ (2 : ℝ) * |L1 t' - L1 t| →
          (0 : ℝ) ≤ B →
            |L1 t' - L1 t| ≤ R →
              |L1 t' - L1 t - L2 t * (t' - t)| ≤ B * |t' - t| ^ (2 : ℕ) / (2 : ℝ) →
                |L t' - L t - L1 t * (t' - t) - L2 t * (t' - t) ^ (2 : ℕ) / (2 : ℝ)| ≤ B * |t' - t| ^ (3 : ℕ) / (6 : ℝ) →
                  |t' * L1 t' - L t' - (t * L1 t - L t) - t * (L1 t' - L1 t) -
                        (L1 t' - L1 t) ^ (2 : ℕ) / ((2 : ℝ) * L2 t)| ≤
                    ((4 : ℝ) * B ^ (2 : ℕ) * R + (2 : ℝ) * B) * |L1 t' - L1 t| ^ (3 : ℕ) := by
  intro L L1 L2 t t' B R ha hd hB hR h2 h3
  set d := t' - t with hd_def
  set D := L1 t' - L1 t with hD_def
  set a := L2 t
  set e3 := L t' - L t - L1 t * d - a * d ^ 2 / 2 with he3
  have ha0 : 0 < a := by linarith
  have key : t' * L1 t' - L t' - (t * L1 t - L t) - t * D - D ^ 2 / (2 * a)
      = -((D - a * d) ^ 2 / (2 * a)) - e3 := by
    rw [he3, hd_def, hD_def]; field_simp; ring
  rw [key]
  have hDabs : 0 ≤ |D| := abs_nonneg _
  have hR0 : 0 ≤ R := le_trans hDabs hR
  have hd4 : |d| ^ 4 ≤ 16 * R * |D| ^ 3 := by
    have h1 : |d| ^ 4 ≤ (2 * |D|) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hd 4
    have h2' : |D| ^ 4 ≤ R * |D| ^ 3 := by
      have := mul_le_mul_of_nonneg_right hR (pow_nonneg hDabs 3); nlinarith
    nlinarith
  have hd3 : |d| ^ 3 ≤ 8 * |D| ^ 3 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hd 3; nlinarith
  have hsq : (D - a * d) ^ 2 ≤ (B * |d| ^ 2 / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hfirst : |(D - a * d) ^ 2 / (2 * a)| ≤ 4 * B ^ 2 * R * |D| ^ 3 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have : (B * |d| ^ 2 / 2) ^ 2 = B ^ 2 * |d| ^ 4 / 4 := by ring
    have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
    have h4 : B ^ 2 * |d| ^ 4 ≤ B ^ 2 * (16 * R * |D| ^ 3) := mul_le_mul_of_nonneg_left hd4 hB2
    have h5 : 0 ≤ 4 * B ^ 2 * R * |D| ^ 3 := by positivity
    nlinarith
  have hsecond : |e3| ≤ 2 * B * |D| ^ 3 := by
    have := mul_le_mul_of_nonneg_left hd3 hB
    calc |e3| ≤ B * |d| ^ 3 / 6 := h3
      _ ≤ 2 * B * |D| ^ 3 := by nlinarith [pow_nonneg hDabs 3]
  calc |-((D - a * d) ^ 2 / (2 * a)) - e3| ≤ |(D - a * d) ^ 2 / (2 * a)| + |e3| := by
        rw [abs_sub_comm]; refine (abs_sub _ _).trans ?_; rw [abs_neg]; linarith
    _ ≤ _ := by nlinarith
