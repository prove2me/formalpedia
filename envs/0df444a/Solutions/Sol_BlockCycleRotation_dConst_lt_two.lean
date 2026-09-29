-- Prove2me | solution 1 for BlockCycleRotation.dConst_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:35:25.78611+00:00
-- url     : https://prove2.me/submissions/c6820005-7837-4a13-b578-2b58057ad4b2

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_cConst_le_partial_add_sharp
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

set_option maxHeartbeats 4000000 in
-- 127 nonzero rational terms with a 32-digit common denominator.
/-- The truncated series for `C` at `a ≤ 20`. -/
theorem cConst_partial_le :
    (∑ a ∈ Finset.range 21, ∑ a' ∈ Finset.range a, cTerm (a, a')) ≤ 39 / 200 := by
  norm_num [cTerm, Finset.sum_range_succ]

/-- **`C < 1/4`.** -/
theorem cConst_lt_quarter : cConst < 1 / 4 := by
  have h := cConst_le_partial_add_sharp (N := 20) (by norm_num)
  have h2 := cConst_partial_le
  norm_num at h
  linarith

end BlockCycleRotation

open BlockCycleRotation in
/-- **`D < 2`**: on average the block cycle scheme uses fewer than two moves per
element, hence fewer than trinity rotation, which uses essentially `2n`. -/
theorem solution : dConst < 2:= by
  rw [dConst]
  linarith [cConst_lt_quarter]
