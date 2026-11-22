-- Prove2me | solution 2 for BlockCycleRotation.add_Outt_le_one
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T12:12:40.516169+00:00
-- url     : https://prove2.me/submissions/71363e7a-c6f2-4e30-83ad-ac3efdc3d7b1

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem solution {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : x + Outt x ≤ 1 := by
  unfold Outt
  split_ifs with h
  · rw [h]; norm_num
  · have hx0' : 0 < x := lt_of_le_of_ne hx0 (Ne.symm h)
    have h2 : (2 : ℝ) ≤ 1 / x := by
      rw [le_div_iff₀ hx0']
      linarith
    have hm2 : (2 : ℝ) ≤ ((⌊1 / x⌋ : ℤ) : ℝ) := by
      have : (2 : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.2 (by exact_mod_cast h2)
      exact_mod_cast this
    have heq : x * (1 + Int.fract (1 / x)) = 1 + x - ((⌊1 / x⌋ : ℤ) : ℝ) * x := by
      rw [Int.fract]
      field_simp
      ring
    rw [heq]
    nlinarith
