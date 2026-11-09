-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail11_actual_reserve_outside_any_band_deficit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:26:30.888277+00:00
-- url     : https://prove2.me/submissions/faf49f1a-aaf0-4e4a-b63d-2a2c501fc396

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_cell_outside_any_positive_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- A real positive reserve outside any prescribed compact band can have an
arbitrarily negative source-exact singular affine HJB grid-cell contribution. -/
theorem solution (K : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ y : ℝ,
      0 < y ∧ y < a / 2 ∧ y < 1 ∧
      (1 / ((K : ℝ) + 4)) *
        (3 + y - 4 * Real.sqrt y - 2 / Real.sqrt y) ≤ -(K : ℝ) := by
  obtain ⟨t, ht0, htband, htsq, hbound⟩ :=
    avram_bv_tail11_singular_cell_outside_any_positive_band K a ha
  let d : ℝ := (K : ℝ) + 4
  let h : ℝ := 1 / d
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hd4 : (4 : ℝ) ≤ d := by
    dsimp [d]
    exact le_add_of_nonneg_left (Nat.cast_nonneg K)
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hle : h ≤ (1 / 4 : ℝ) := by
    dsimp [h]
    apply (div_le_iff₀ hd).2
    nlinarith [hd4]
  have hprod : 0 ≤ ((1 / 4 : ℝ) - h) * (1 / 4 + h) :=
    mul_nonneg (sub_nonneg.mpr hle) (add_nonneg (by norm_num) hh.le)
  have hsq_le : h ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith [hprod]
  have htsq' : t ≤ h ^ 2 := by simpa [h, d] using htsq
  have ht1 : t < 1 := by linarith
  have hpositive : 0 < t * (1 - t) :=
    mul_pos ht0 (sub_pos.mpr ht1)
  have hsquare : t ^ 2 < t := by nlinarith [hpositive]
  have hy0 : 0 < t ^ 2 := pow_pos ht0 2
  have hyband : t ^ 2 < a / 2 := lt_trans hsquare htband
  have hy1 : t ^ 2 < 1 := lt_trans hsquare ht1
  have hsqrt : Real.sqrt (t ^ 2) = t := by
    simpa [abs_of_pos ht0] using Real.sqrt_sq_eq_abs t
  refine ⟨t ^ 2, hy0, hyband, hy1, ?_⟩
  simpa only [hsqrt] using hbound
