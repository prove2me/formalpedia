-- Prove2me | solution 1 for BookProof.ChapterH4.sirk_le_sia
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:26:54.959357+00:00
-- url     : https://prove2.me/submissions/5c2f3906-6529-45ea-abfc-463a62a40a7e

-- Generated from ChapterH4.lean — solution of BookProof.ChapterH4.sirk_le_sia
import Mathlib
import Definitions.Def_ChapterH4
open BookProof.ChapterH4










open scoped BigOperators


noncomputable section





variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (C Dmin h m normv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ normv)
    (hh : 0 ≤ h) (hm : 0 ≤ m) :
    2 * C * Real.exp (-(h * m)) * Dmin * normv ≤ 2 * C * Dmin * normv := by

  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith))) hD) hnv
