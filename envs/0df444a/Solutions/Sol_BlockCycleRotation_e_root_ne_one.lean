-- Prove2me | solution 1 for BlockCycleRotation.e_root_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:28:42.966339+00:00
-- url     : https://prove2.me/submissions/c359b0cf-97c4-4666-a2e7-3ab2ccd70701

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_four_mul_min_div_le_norm
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

end BlockCycleRotation

open BlockCycleRotation in
/-- A nontrivial `a`-th root of unity is not `1`. -/
theorem solution {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    e (2 * π * (m : ℝ) / a) ≠ 1:= by
  have hapos : 0 < a := lt_trans h0 hma
  have ha : (0 : ℝ) < a := by exact_mod_cast hapos
  have hminpos : 0 < min m (a - m) := by omega
  have hmr : (0 : ℝ) < ((min m (a - m) : ℕ) : ℝ) := by exact_mod_cast hminpos
  have hlow := four_mul_min_div_le_norm h0 hma
  have hden : 0 < ‖e (2 * π * (m : ℝ) / a) - 1‖ := by
    have hp : (0 : ℝ) < 4 * ((min m (a - m) : ℕ) : ℝ) / a := by positivity
    linarith
  intro hc
  rw [hc, sub_self, norm_zero] at hden
  exact lt_irrefl 0 hden
