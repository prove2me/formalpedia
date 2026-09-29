-- Prove2me | solution 1 for BlockCycleRotation.cTerm_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:34:24.878134+00:00
-- url     : https://prove2.me/submissions/2986a3de-2bec-4673-aa90-3a57c9abe97d

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
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

end BlockCycleRotation

open BlockCycleRotation in
/-- **Sharper termwise bound.**  `cTerm ≤ 1/a³`. -/
theorem solution (p : ℕ × ℕ) : cTerm p ≤ 1 / (p.1 : ℝ) ^ 3:= by
  unfold cTerm
  split
  · rename_i h
    obtain ⟨h1, h2, -⟩ := h
    have hp1 : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    have hp2 : (0 : ℝ) ≤ (p.2 : ℝ) := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hp1 2, mul_nonneg hp1.le hp2, mul_nonneg hp2 hp2,
      mul_nonneg (mul_nonneg hp1.le hp1.le) hp2]
  · positivity
