-- Prove2me | solution 1 for BookProof.ChapterSternGerlach.dft_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:43.367417+00:00
-- url     : https://prove2.me/submissions/fae6e8d8-e989-45d0-8306-f60a6566d96c

-- Generated from ChapterSternGerlach.lean — solution of BookProof.ChapterSternGerlach.dft_unitary
import Mathlib
import Definitions.Def_ChapterSternGerlach
import Theorems.Thm_BookProof_ChapterSternGerlach_dft_geom_sum_zero
open BookProof.ChapterSternGerlach




open Complex Matrix Finset

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : 0 < n) :
    dftMatrix n * star (dftMatrix n) = 1 := by

  ext i k
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, dftMatrix, Matrix.one_apply]
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((i.val : ℂ) - k.val) / n) with hwdef
  have key : ∀ j : Fin n,
      Complex.exp (2 * Real.pi * Complex.I * (i.val * j.val) / n) / (Real.sqrt n : ℂ) *
        star (Complex.exp (2 * Real.pi * Complex.I * (k.val * j.val) / n) / (Real.sqrt n : ℂ))
      = w ^ (j.val) / n := by
    intro j
    rw [hwdef, star_div₀, Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj]
    have hconj : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (k.val * j.val) / n)
        = - (2 * Real.pi * Complex.I * (k.val * j.val) / n) := by
      simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_natCast]
      ring
    rw [hconj, ← Complex.exp_nat_mul, div_mul_div_comm, ← Complex.exp_add]
    congr 1
    · congr 1; ring
    · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), Complex.ofReal_natCast]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun m => w ^ m)]
  by_cases hik : i = k
  · subst hik
    have hw1 : w = 1 := by rw [hwdef]; simp
    rw [hw1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, if_true]
    field_simp
  · have hwn : w ^ n = 1 := by
      rw [hwdef, ← Complex.exp_nat_mul]
      have heq : (n : ℂ) * (2 * Real.pi * Complex.I * ((i.val : ℂ) - k.val) / n)
          = (((i.val : ℤ) - k.val : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; field_simp
      rw [heq, Complex.exp_int_mul_two_pi_mul_I]
    have hwne : w ≠ 1 := by
      rw [hwdef, Ne, Complex.exp_eq_one_iff]
      rintro ⟨m, hm⟩
      have hA : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : ((i.val : ℂ) - k.val) = (m : ℂ) * n := by
        field_simp at hm
        linear_combination hm
      have hint : ((i.val : ℤ) - k.val) = m * n := by exact_mod_cast h2
      have hdvd : (n : ℤ) ∣ ((i.val : ℤ) - k.val) := ⟨m, by linarith [hint]⟩
      have hdne : ((i.val : ℤ) - k.val) ≠ 0 := by
        intro h; apply hik; apply Fin.ext; omega
      have hle : (n : ℤ) ≤ |((i.val : ℤ) - k.val)| :=
        Int.le_of_dvd (abs_pos.mpr hdne) ((dvd_abs _ _).mpr hdvd)
      have hbi : (i.val : ℤ) < n := by exact_mod_cast i.isLt
      have hbk : (k.val : ℤ) < n := by exact_mod_cast k.isLt
      have hub : |((i.val : ℤ) - k.val)| < n := by rw [abs_lt]; omega
      linarith [hle, hub]
    rw [dft_geom_sum_zero n w hwne hwn, zero_div, if_neg hik]
