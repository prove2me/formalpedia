-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_integrand_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:07:18.318498+00:00
-- url     : https://prove2.me/submissions/647e9a91-0848-4813-8430-fe2e75d8f193

import Mathlib

open Set

theorem solution (θ y : ℝ) (hθ : 1 ≤ θ) (hy : y < 0) :
    |Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y|
        ≤ θ ^ 2 * min 1 (y ^ 2) ∧
    Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y
        ≤ (Ioo (-1 : ℝ) 0).indicator (fun t : ℝ => θ ^ 2 * t ^ 2) y := by
  have hθ0 : 0 ≤ θ := by linarith
  have hz : θ * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hθ0 (le_of_lt hy)
  have hθsq : 1 ≤ θ ^ 2 := by nlinarith
  by_cases hsmall : -1 < y
  · have hs : y ∈ Ioo (-1 : ℝ) 0 := ⟨hsmall, hy⟩
    have hi : y ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
    have hy2 : y ^ 2 ≤ 1 := by
      have h : 0 ≤ (1 + y) * (1 - y) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hlo : 0 ≤ Real.exp (θ * y) - 1 - θ * y := by
      linarith [Real.add_one_le_exp (θ * y)]
    have hhi : Real.exp (θ * y) - 1 - θ * y ≤ (θ * y) ^ 2 := by
      by_cases hnear : -1 ≤ θ * y
      · have hnorm : |θ * y| ≤ 1 := abs_le.mpr ⟨hnear, by linarith⟩
        exact (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hnorm)
      · have hfar : θ * y ≤ -1 := le_of_not_ge hnear
        have he : Real.exp (θ * y) ≤ 1 :=
          Real.exp_le_one_iff.mpr hz
        have hh : 0 ≤ (-(θ * y)) * (-(θ * y) - 1) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [hh]
    simp only [Set.indicator_of_mem hi, Set.indicator_of_mem hs,
      mul_one, min_eq_right hy2]
    constructor
    · rw [abs_of_nonneg (by nlinarith [hlo])]
      nlinarith [hhi]
    · nlinarith [hhi]
  · have hfar : y ≤ -1 := le_of_not_gt hsmall
    have hi : y ∉ Ioo (-1 : ℝ) 1 := by
      simp only [mem_Ioo]
      intro h
      linarith [h.1]
    have hs : y ∉ Ioo (-1 : ℝ) 0 := by
      simp only [mem_Ioo]
      intro h
      linarith [h.1]
    have hy2 : 1 ≤ y ^ 2 := by
      have h : 0 ≤ (-y - 1) * (-y + 1) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hexp : Real.exp (θ * y) ≤ 1 :=
      Real.exp_le_one_iff.mpr hz
    have hexppos : 0 < Real.exp (θ * y) :=
      Real.exp_pos _
    have hI1 :
        (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y = 0 := by
      simp [Set.indicator, hi]
    have hI2 :
        (Ioo (-1 : ℝ) 0).indicator (fun t : ℝ => θ ^ 2 * t ^ 2) y = 0 := by
      simp [Set.indicator, hs]
    simp only [hI1, hI2, mul_zero, sub_zero, min_eq_left hy2, mul_one]
    constructor
    · rw [abs_of_nonpos (by linarith)]
      linarith [hθsq, hexppos]
    · linarith [hexp]
