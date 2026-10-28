-- Prove2me | solution 1 for BitDFT.boundary_signed_encoding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T20:44:23.844075+00:00
-- url     : https://prove2.me/submissions/12aaf804-cd36-4aae-bda7-ddff4160aa6a

import Definitions.Def_BitDFT_Encoding
import Theorems.Thm_BitDFT_boundary_shift_encoding
import Mathlib.Tactic

set_option autoImplicit false
open BitDFT IntMul

theorem solution (w q : ℕ) (z : ℤ) :
    encInt (w+q) (z * (2^q : ℤ)) =
      [decide (z < 0)] ++ bin w z.natAbs ++ List.replicate q false := by
  have hpos : 0 < (2^q : ℤ) := by positivity
  have hs : decide (z * (2^q : ℤ) < 0) = decide (z < 0) := by
    by_cases hz : z < 0
    · have hp : z * (2^q : ℤ) < 0 := mul_neg_of_neg_of_pos hz hpos
      simp [hz, hp]
    · have hz0 : 0 ≤ z := le_of_not_gt hz
      have hp : 0 ≤ z * (2^q : ℤ) := mul_nonneg hz0 (le_of_lt hpos)
      simp [hz, not_lt.mpr hp]
  have hn : (z * (2^q : ℤ)).natAbs = z.natAbs * 2^q := by
    simp [Int.natAbs_mul]
  simp only [encInt, hs, hn]
  rw [BitDFT.boundary_shift_encoding]
  simp
