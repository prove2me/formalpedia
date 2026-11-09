-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail11_singular_cell_below_band_lower_edge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:08:09.129416+00:00
-- url     : https://prove2.me/submissions/68f2ab5c-01a8-4fcc-9b16-caedb81bf9bb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

/-- A small physical-grid reserve lies strictly below the compact-band lower edge,
while retaining an arbitrarily negative singular signed generator cell. -/
theorem solution (K : ℕ) (t : ℝ) (ht : 0 < t)
    (ht_bound : t ≤ (1 / ((K : ℝ) + 4)) ^ 2) :
    t < (1 / ((K : ℝ) + 4)) / 2 ∧
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
  have hle : h ≤ (1 / 4 : ℝ) := by
    dsimp [h]
    apply (div_le_iff₀ hd).2
    nlinarith [hd4]
  have hlt : h < (1 / 2 : ℝ) :=
    lt_of_le_of_lt hle (by norm_num)
  have hprod : 0 < h * ((1 / 2 : ℝ) - h) :=
    mul_pos hh (sub_pos.mpr hlt)
  have hsq_lt : h ^ 2 < h / 2 := by
    nlinarith [hprod]
  have ht_cell : t ≤ h ^ 2 := by
    simpa [h, d] using ht_bound
  constructor
  · change t < h / 2
    exact lt_of_le_of_lt ht_cell hsq_lt
  · exact avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
      K t ht ht_bound
