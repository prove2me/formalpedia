-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T10:23:39.78897+00:00
-- url     : https://prove2.me/submissions/7d68ac1c-5920-4707-b565-b34c855b39d8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_profile_tail_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- The signed original singular generator contribution is unbounded below
uniformly over a shrinking positive reserve neighbourhood. -/
theorem solution (K : ℕ) (t : ℝ) (ht : 0 < t)
    (ht_bound : t ≤ (1 / ((K : ℝ) + 4)) ^ 2) :
    (1 / ((K : ℝ) + 4)) *
      (3 + t ^ 2 - 4 * t - 2 / t) ≤ -(K : ℝ) := by
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
  have ht_cell : t ≤ h ^ 2 := by
    simpa [h, d] using ht_bound
  have htsmall : t ≤ (1 / 4 : ℝ) := le_trans ht_cell hsmall
  have hp := avram_a19_singular_profile_tail_bound t ht htsmall
  have hmul := mul_le_mul_of_nonneg_left hp hh.le
  have hunit : h * d = 1 := by
    dsimp [h]
    field_simp [ne_of_gt hd]
  have hsq : h ^ 2 * d = h := by
    calc
      h ^ 2 * d = h * (h * d) := by ring
      _ = h := by rw [hunit]; ring
  have ht_d : t * d ≤ h := by
    calc
      t * d ≤ h ^ 2 * d := mul_le_mul_of_nonneg_right ht_cell hd.le
      _ = h := hsq
  have hdiv : d ≤ h / t := (le_div_iff₀ ht).2 (by simpa [mul_comm] using ht_d)
  have hsource :
      h * (3 + t ^ 2 - 4 * t - 2 / t) ≤ -(h / t) := by
    calc
      _ ≤ -(h * (1 / t)) := by nlinarith [hmul]
      _ = -(h / t) := by simp [div_eq_mul_inv]
  have hb : h * (3 + t ^ 2 - 4 * t - 2 / t) ≤ -d := by
    linarith
  have hgoal : h * (3 + t ^ 2 - 4 * t - 2 / t) ≤ -(K : ℝ) := by
    calc
      _ ≤ -d := hb
      _ ≤ -(K : ℝ) := by dsimp [d]; nlinarith
  simpa [h, d] using hgoal
