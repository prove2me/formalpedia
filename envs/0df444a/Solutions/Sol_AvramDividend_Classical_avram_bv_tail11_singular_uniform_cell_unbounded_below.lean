-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail11_singular_uniform_cell_unbounded_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T10:00:39.782652+00:00
-- url     : https://prove2.me/submissions/c50bdec9-7225-47f5-ac40-d6ef757d8016

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_profile_tail_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- A source-exact scalar obstruction: one original affine singular HJB
generator sample, weighted by its unit-horizon physical cell width, has
arbitrarily large negative magnitude. -/
theorem solution (K : ℕ) :
    let h : ℝ := 1 / ((K : ℝ) + 4)
    h * (3 + h ^ 4 - 4 * h ^ 2 - 2 / h ^ 2) ≤ -(K : ℝ) := by
  dsimp
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
  have hle : h ≤ (1 / 2 : ℝ) := by
    dsimp [h]
    apply (div_le_iff₀ hd).2
    nlinarith [hd4]
  have hsmall : h ^ 2 ≤ (1 / 4 : ℝ) := by
    have hprod : 0 ≤ (1 / 2 - h) * (1 / 2 + h) :=
      mul_nonneg (sub_nonneg.mpr hle)
        (add_nonneg (by norm_num) hh.le)
    nlinarith [hprod]
  have ht : 0 < h ^ 2 := pow_pos hh _
  have hp := avram_a19_singular_profile_tail_bound (h ^ 2) ht hsmall
  have hmul := mul_le_mul_of_nonneg_left hp hh.le
  have hcell :
      h * (3 + h ^ 4 - 4 * h ^ 2 - 2 / h ^ 2) ≤
        -(h * (1 / h ^ 2)) := by
    nlinarith [hmul]
  have hquot : h * (1 / h ^ 2) = d := by
    dsimp [h]
    field_simp [ne_of_gt hd]
    <;> ring
  have result : h * (3 + h ^ 4 - 4 * h ^ 2 - 2 / h ^ 2) ≤
      -(K : ℝ) := by
    calc
      _ ≤ -d := by nlinarith [hcell, hquot]
      _ ≤ -(K : ℝ) := by
        dsimp [d]
        nlinarith
  simpa [h, d] using result
