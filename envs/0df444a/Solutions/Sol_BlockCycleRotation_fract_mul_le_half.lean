-- Prove2me | solution 1 for BlockCycleRotation.fract_mul_le_half
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T11:55:41.647364+00:00
-- url     : https://prove2.me/submissions/34b81396-bc78-49d1-b17f-0d364d199b62

import Mathlib

open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

theorem solution {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1) :
    g * Int.fract (1 / g) ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hg0 with h | hg
  · rw [← h]; simp
  · have hm : (1 : ℝ) < 1 / g := by rw [lt_div_iff₀ hg]; linarith
    have hm1 : (1 : ℝ) ≤ ((⌊1 / g⌋ : ℤ) : ℝ) := by
      have : (1 : ℤ) ≤ ⌊1 / g⌋ := Int.le_floor.2 (by exact_mod_cast le_of_lt hm)
      exact_mod_cast this
    have hlt : 1 / g < ((⌊1 / g⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hub : 1 < (((⌊1 / g⌋ : ℤ) : ℝ) + 1) * g := (div_lt_iff₀ hg).1 hlt
    rw [Int.fract]
    have heq : g * (1 / g - ((⌊1 / g⌋ : ℤ) : ℝ)) = 1 - g * ((⌊1 / g⌋ : ℤ) : ℝ) := by
      field_simp
    rw [heq]
    nlinarith [hub, hm1, hg,
      mul_lt_mul_of_pos_left hub (show (0 : ℝ) < ((⌊1 / g⌋ : ℤ) : ℝ) by linarith)]
