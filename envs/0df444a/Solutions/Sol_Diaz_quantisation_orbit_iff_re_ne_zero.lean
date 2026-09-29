-- Prove2me | solution 1 for Diaz.quantisation_orbit_iff_re_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T11:03:41.923409+00:00
-- url     : https://prove2.me/submissions/ffc08767-3337-476a-a1a5-a44e51b631a4

import Mathlib
import Theorems.Thm_Diaz_exp_ratio_pow_eq_one_iff

open ComplexConjugate

private theorem polar2_ratMul_re (q : ℚ) (u : ℂ) : ((q : ℂ) * u).re = (q : ℝ) * u.re := by
  simp [Complex.mul_re]

private theorem polar2_ratMul_im (q : ℚ) (u : ℂ) : ((q : ℂ) * u).im = (q : ℝ) * u.im := by
  simp [Complex.mul_im]

theorem solution {u : ℂ} {k : ℤ} (hk : k ≠ 0)
    (him : u.im = (k : ℝ) * Real.pi) :
    (∀ q : ℚ, q ≠ 0 → ∀ m : ℕ, 0 < m →
        (Complex.exp ((q : ℂ) * u) / conj (Complex.exp ((q : ℂ) * u))) ^ m = 1 →
        Real.pi ^ 2 / (m : ℝ) ^ 2 < Complex.normSq ((q : ℂ) * u))
      ↔ u.re ≠ 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  constructor
  · intro h hre
    have hq : ((1 : ℚ) / (k : ℚ)) ≠ 0 := by
      simp [Int.cast_ne_zero.mpr hk]
    have hre' : ((((1 : ℚ) / (k : ℚ) : ℚ) : ℂ) * u).re = 0 := by
      rw [polar2_ratMul_re, hre, mul_zero]
    have him' : ((((1 : ℚ) / (k : ℚ) : ℚ) : ℂ) * u).im = Real.pi := by
      rw [polar2_ratMul_im, him]
      push_cast
      field_simp
    have hcond : (Complex.exp ((((1 : ℚ) / (k : ℚ) : ℚ) : ℂ) * u) /
        conj (Complex.exp ((((1 : ℚ) / (k : ℚ) : ℚ) : ℂ) * u))) ^ 1 = 1 := by
      rw [Diaz.exp_ratio_pow_eq_one_iff]
      exact ⟨1, by rw [him']; push_cast; ring⟩
    have := h ((1 : ℚ) / (k : ℚ)) hq 1 one_pos hcond
    rw [Complex.normSq_apply, hre', him'] at this
    norm_num at this
    nlinarith [Real.pi_pos]
  · intro hre q hq m hm hcond
    rw [Diaz.exp_ratio_pow_eq_one_iff] at hcond
    obtain ⟨n, hn⟩ := hcond
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hqR : (q : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hq
    set y : ℝ := ((q : ℂ) * u).im with hy
    have hyv : y = (q : ℝ) * ((k : ℝ) * Real.pi) := by rw [hy, polar2_ratMul_im, him]
    have hy0 : y ≠ 0 := by
      rw [hyv]
      exact mul_ne_zero hqR (mul_ne_zero hkR (ne_of_gt hpi))
    have hn0 : n ≠ 0 := by
      intro h0
      apply hy0
      have : (m : ℝ) * y = 0 := by rw [hn, h0]; simp
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hmR)
      · exact h
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by omega)
    have hysq : Real.pi ^ 2 / (m : ℝ) ^ 2 ≤ y ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : ((m : ℝ) * y) ^ 2 = ((n : ℝ) * Real.pi) ^ 2 := by rw [hn]
      have h2 : ((n : ℝ) * Real.pi) ^ 2 = (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
      have h3 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [abs_nonneg ((n : ℝ)), sq_abs ((n : ℝ))]
      nlinarith [sq_nonneg ((m : ℝ) * y), Real.pi_pos]
    have hrepos : (0 : ℝ) < ((q : ℂ) * u).re ^ 2 := by
      have : ((q : ℂ) * u).re = (q : ℝ) * u.re := polar2_ratMul_re q u
      rw [this]
      positivity
    rw [Complex.normSq_apply]
    nlinarith [hysq, hrepos]
