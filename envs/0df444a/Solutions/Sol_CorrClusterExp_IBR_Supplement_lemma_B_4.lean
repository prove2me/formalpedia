-- Prove2me | solution 1 for CorrClusterExp.IBR.Supplement.lemma_B_4
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T15:27:01.644238+00:00
-- url     : https://prove2.me/submissions/9e764144-9511-4f37-b129-29c1dfba726a

import Mathlib

namespace CorrClusterExp.IBR.Supplement
end CorrClusterExp.IBR.Supplement
open CorrClusterExp.IBR.Supplement


theorem solution (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (m : ℕ) (hm : 1 ≤ m) (h : ℕ)
    (hh : h ≤ m) (p σ : ℝ) (hp : p = (⌈q * m⌉₊ : ℝ) - q * m)
    (hσ : σ = -((m * q * (1 - q) - p * (1 - p)) / (m * (m - 1) * q * (1 - q)))) :
    (h : ℝ) ^ 2 * (1 / (m : ℝ) + σ) - h * σ ≤ 1 / (2 * q * (1 - q)) + 1 := by
  have hQ : 0 < q * (1 - q) := mul_pos hq0 (by linarith)
  have hR : 0 ≤ 1 / (2 * q * (1 - q)) := div_nonneg zero_le_one (by nlinarith)
  rcases eq_or_lt_of_le hm with h1 | h2
  · -- one cluster: the correlation is a division by zero, hence zero
    subst h1
    have hs : σ = 0 := by rw [hσ]; simp
    have hle : (h : ℝ) ^ 2 * (1 / ((1 : ℕ) : ℝ) + σ) - h * σ ≤ 1 := by
      have : h = 0 ∨ h = 1 := by omega
      rcases this with rfl | rfl <;> simp [hs]
    linarith
  · have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast h2
    have hm1 : (0 : ℝ) < m - 1 := by linarith
    have hm0 : (0 : ℝ) < m := by linarith
    have hp0 : 0 ≤ p := by
      rw [hp]; have := Nat.le_ceil (q * m); linarith
    have hp1 : p < 1 := by
      rw [hp]; have := Nat.ceil_lt_add_one (a := q * m) (by positivity); linarith
    have hden : 0 < (m : ℝ) * (m - 1) * (q * (1 - q)) := mul_pos (mul_pos hm0 hm1) hQ
    have key : (h : ℝ) ^ 2 * (1 / (m : ℝ) + σ) - h * σ
        = ((h : ℝ) * (h - 1) * (p * (1 - p)) + h * (m - h) * (q * (1 - q)))
          / ((m : ℝ) * (m - 1) * (q * (1 - q))) := by
      have a : q ≠ 0 := hq0.ne'
      have b : 1 - q ≠ 0 := by
        have : 0 < 1 - q := by linarith
        exact this.ne'
      have c : (m : ℝ) - 1 ≠ 0 := hm1.ne'
      have d : (m : ℝ) ≠ 0 := hm0.ne'
      rw [hσ]
      field_simp
      ring
    have hhm : (h : ℝ) ≤ m := by exact_mod_cast hh
    have hh01 : 0 ≤ (h : ℝ) * (h - 1) ∧ (h : ℝ) * (h - 1) ≤ m * (m - 1) := by
      rcases Nat.eq_zero_or_pos h with h0 | hpos
      · subst h0
        simp only [Nat.cast_zero, zero_mul, le_refl, true_and]
        exact mul_nonneg hm0.le hm1.le
      · have : (1 : ℝ) ≤ h := by exact_mod_cast hpos
        exact ⟨mul_nonneg (by linarith) (by linarith),
          mul_le_mul hhm (by linarith) (by linarith) hm0.le⟩
    have hP : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    have hP0 : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
    have a : (h : ℝ) * (h - 1) * (p * (1 - p)) ≤ m * (m - 1) * (1 / 4) :=
      mul_le_mul hh01.2 hP hP0 (mul_nonneg hm0.le hm1.le)
    have b : (h : ℝ) * (m - h) * (q * (1 - q)) ≤ (m : ℝ) ^ 2 / 4 * (q * (1 - q)) :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ((h : ℝ) - m / 2)]) hQ.le
    have c : (m : ℝ) ^ 2 / 4 * (q * (1 - q)) ≤ m * (m - 1) * (q * (1 - q)) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hQ.le
    rw [key, div_le_iff₀ hden]
    have e : (1 / (2 * q * (1 - q)) + 1) * ((m : ℝ) * (m - 1) * (q * (1 - q)))
        = m * (m - 1) / 2 + m * (m - 1) * (q * (1 - q)) := by
      have a : q ≠ 0 := hq0.ne'
      have b : 1 - q ≠ 0 := by
        have : 0 < 1 - q := by linarith
        exact this.ne'
      field_simp
    rw [e]
    nlinarith [mul_nonneg hm0.le hm1.le]
