-- Prove2me | solution 2 for AvramDividend.Classical.barrierValue_zero_of_finite_jump_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:53:00.573738+00:00
-- url     : https://prove2.me/submissions/ebac1d8b-8b00-46fd-ac42-7dbeda62b180

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_eq_ratio_of_finite_derivZeroPlus
import Mathlib.Data.EReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- Evaluate the finite-activity barrier normaliser from its scale data. -/
theorem solution
    (W : ℝ → ℝ) (q lam d : ℝ)
    (hd : d ≠ 0) (hql : q + lam ≠ 0)
    (hW0 : W 0 = 1 / d)
    (hWder : derivZeroPlus W = (((q + lam) / d ^ 2 : ℝ) : EReal)) :
    barrierValue W 0 0 = d / (q + lam) := by
  rw [barrierValue_zero_eq_ratio_of_finite_derivZeroPlus W ((q + lam) / d ^ 2) hWder, hW0]
  field_simp [hd, hql] <;> ring
