-- Prove2me | solution 1 for BlockCycleRotation.dConst_le_185
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:22:14.214071+00:00
-- url     : https://prove2.me/submissions/912ff1a1-debf-4389-8f67-168a0a4f4db6

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_cConst_le_seventeen_eightieths
import Mathlib

open Real Finset Filter Topology

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

end BlockCycleRotation

open BlockCycleRotation in
/-- **`D ≤ 1.85`**, the value quoted in the paper. -/
theorem solution : dConst ≤ 1.85:= by
  rw [dConst]
  have h := cConst_le_seventeen_eightieths
  norm_num
  linarith
