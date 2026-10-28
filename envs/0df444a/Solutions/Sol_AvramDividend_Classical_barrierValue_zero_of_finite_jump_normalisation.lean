-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_zero_of_finite_jump_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:52:29.993966+00:00
-- url     : https://prove2.me/submissions/9f1c58b7-369e-4aca-8807-9521d38efba0

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_eq_ratio_of_finite_derivZeroPlus

open AvramDividend.Classical

/-- The finite-activity zero-barrier analytic normaliser, conditional on the
    scale function origin and right-derivative identities. -/
theorem solution
    (W : ℝ → ℝ) (q lam d : ℝ)
    (hd : d ≠ 0) (hql : q + lam ≠ 0)
    (hW0 : W 0 = 1 / d)
    (hWder : derivZeroPlus W = (((q + lam) / d ^ 2 : ℝ) : EReal)) :
    barrierValue W 0 0 = d / (q + lam) := by
  rw [AvramDividend.Classical.barrierValue_zero_eq_ratio_of_finite_derivZeroPlus W _ hWder, hW0]
  field_simp
