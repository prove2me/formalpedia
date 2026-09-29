-- Prove2me | solution 1 for BlockCycleRotation.two_div_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:29:43.708408+00:00
-- url     : https://prove2.me/submissions/1dd4925c-df33-4620-aed2-526ffda2cc2b

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
/-- The chord bound in the form the sum estimates use. -/
theorem solution {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    2 / ‖e (2 * π * (m : ℝ) / a) - 1‖ ≤ (a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)):= by
  have hapos : 0 < a := lt_trans h0 hma
  have ha : (0 : ℝ) < a := by exact_mod_cast hapos
  have hminpos : 0 < min m (a - m) := by omega
  have hmr : (0 : ℝ) < ((min m (a - m) : ℕ) : ℝ) := by exact_mod_cast hminpos
  have hlow := four_mul_min_div_le_norm h0 hma
  have hden : 0 < ‖e (2 * π * (m : ℝ) / a) - 1‖ := by
    have hp : (0 : ℝ) < 4 * ((min m (a - m) : ℕ) : ℝ) / a := by positivity
    linarith
  rw [div_le_div_iff₀ hden (by positivity)]
  have hmul : 4 * ((min m (a - m) : ℕ) : ℝ) ≤ (a : ℝ) * ‖e (2 * π * (m : ℝ) / a) - 1‖ := by
    have hstep := mul_le_mul_of_nonneg_left hlow ha.le
    calc (4 : ℝ) * ((min m (a - m) : ℕ) : ℝ)
        = (a : ℝ) * (4 * ((min m (a - m) : ℕ) : ℝ) / a) := by field_simp
      _ ≤ (a : ℝ) * ‖e (2 * π * (m : ℝ) / a) - 1‖ := hstep
  linarith
