-- Prove2me | solution 1 for BookProof.ChapterE4.cross_diag_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:32:06.398465+00:00
-- url     : https://prove2.me/submissions/19692a67-d031-4264-9ba3-95121de25232

-- Generated from ChapterE4.lean — solution of BookProof.ChapterE4.cross_diag_zero
import Mathlib
import Definitions.Def_ChapterE4
import Theorems.Thm_BookProof_ChapterE4_wave_eq_zero_of_lt
open BookProof.ChapterE4



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (s d i : ℕ) :
    basisVec s i * wave θ (s + 1) d i = 0 := by

  by_cases hi : i = s <;> simp only [basisVec, hi, mul_eq_zero, ne_eq, not_false_eq_true,
      Pi.single_eq_of_ne, zero_mul];
  exact Or.inr ( wave_eq_zero_of_lt _ _ _ _ ( Nat.lt_succ_self _ ) )
