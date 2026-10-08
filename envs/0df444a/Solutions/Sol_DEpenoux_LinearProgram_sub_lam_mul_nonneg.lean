-- Prove2me | solution 1 for DEpenoux.LinearProgram.sub_lam_mul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:06:12.604126+00:00
-- url     : https://prove2.me/submissions/8353f57c-9eaa-416e-a332-46654ebbb211

import Mathlib

theorem solution {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (hP0 : ∀ i k, 0 ≤ P i k) (hP1 : ∀ i, ∑ k, P i k = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (u : Fin m → ℝ)
    (h : ∀ i, 0 ≤ u i - lam * Matrix.mulVec P u i) :
    ∀ i, 0 ≤ u i := by
  intro i
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ u ⟨i, Finset.mem_univ i⟩
  have hPu : u j ≤ Matrix.mulVec P u j := by
    show u j ≤ ∑ k, P j k * u k
    calc u j = ∑ k, P j k * u j := by rw [← Finset.sum_mul, hP1, one_mul]
      _ ≤ ∑ k, P j k * u k :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hj k (Finset.mem_univ k)) (hP0 j k)
  have h1 := h j
  have h2 : lam * u j ≤ lam * Matrix.mulVec P u j := mul_le_mul_of_nonneg_left hPu hlam0.le
  have h3 : 0 ≤ u j := by nlinarith
  linarith [hj i (Finset.mem_univ i)]
