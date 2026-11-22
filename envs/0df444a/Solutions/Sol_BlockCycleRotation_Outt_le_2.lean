-- Prove2me | solution 2 for BlockCycleRotation.Outt_le
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T12:06:27.153882+00:00
-- url     : https://prove2.me/submissions/58f65073-41e6-4bc3-ad3a-01ebaf380804

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem solution {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Outt x ≤ 2 / 3 := by
  unfold Outt
  split_ifs with h
  · norm_num
  · have hx0' : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h)
    have h2 : (2 : ℝ) ≤ 1 / x := by
      rw [le_div_iff₀ hx0']
      linarith
    have hm2 : (2 : ℝ) ≤ ((⌊1 / x⌋ : ℤ) : ℝ) := by
      have : (2 : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.2 (by exact_mod_cast h2)
      exact_mod_cast this
    have hfl' : 1 / x < ((⌊1 / x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hub : 1 < (((⌊1 / x⌋ : ℤ) : ℝ) + 1) * x := (div_lt_iff₀ hx0').1 hfl'
    have heq : x * (1 + Int.fract (1 / x)) = 1 - (((⌊1 / x⌋ : ℤ) : ℝ) - 1) * x := by
      rw [Int.fract]
      field_simp
      ring
    rw [heq]
    nlinarith [hub, hm2, hx0']
