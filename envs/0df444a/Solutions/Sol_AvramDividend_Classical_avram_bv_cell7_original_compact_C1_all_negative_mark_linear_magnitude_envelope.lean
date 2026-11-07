-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_compact_C1_all_negative_mark_linear_magnitude_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:47:11.56186+00:00
-- url     : https://prove2.me/submissions/33172b02-e7d7-474f-8be0-cca54eb81889

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- A compact-band C1 negative-mark difference is bounded linearly by the
    actual negative-mark magnitude, across both small and large marks. -/
theorem solution
    (w : ℝ → ℝ) (a b L R : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (y z : ℝ) (hy : y ∈ Icc a b) (hz : z < 0) :
    |w (y + z) - w y| ≤ (L + 4 * R / a) * (-z) := by
  have hznonneg : 0 ≤ -z := by linarith
  have hRdiv : 0 ≤ 4 * R / a :=
    div_nonneg (by nlinarith [hR]) (le_of_lt ha)
  by_cases hsmall : -z ≤ a / 2
  · have hy0 : y ∈ Icc (a / 2) b := by
      constructor
      · change a / 2 ≤ y
        nlinarith [hy.1]
      · exact hy.2
    have hyz : y + z ∈ Icc (a / 2) b := by
      constructor
      · change a / 2 ≤ y + z
        nlinarith [hy.1, hsmall]
      · change y + z ≤ b
        linarith [hy.2]
    have h := hLip (y + z) hyz y hy0
    have hdelta : |(y + z) - y| = -z := by
      have ht : (y + z) - y = z := by ring
      rw [ht, abs_of_neg hz]
    rw [hdelta] at h
    nlinarith [mul_nonneg hRdiv hznonneg]
  · have hlarge : a / 2 ≤ -z := by
      have hl : a / 2 < -z := lt_of_not_ge hsmall
      exact le_of_lt hl
    have hW1 : |w (y + z)| ≤ R :=
      hWbound (y + z) (by linarith [hy.2])
    have hW2 : |w y| ≤ R := hWbound y hy.2
    have htri := abs_sub_le (w (y + z)) 0 (w y)
    simp only [sub_zero, zero_sub, abs_neg] at htri
    have hdiff : |w (y + z) - w y| ≤ 2 * R := by
      linarith
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hscale : (4 * R / a) * (a / 2) = 2 * R := by
      field_simp [ha0]
      ring
    have hmul : 2 * R ≤ (4 * R / a) * (-z) := by
      nlinarith [mul_le_mul_of_nonneg_left hlarge hRdiv]
    nlinarith [mul_nonneg hL hznonneg]
