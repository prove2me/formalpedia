-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a83_original_gaussian_uniform_mesh_time_mass_le_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:07:38.538472+00:00
-- url     : https://prove2.me/submissions/03e7644e-73ab-4d31-b54a-508d0701856b

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal

/-- The genuine original (m+1)-denominator Gaussian physical uniform grid occupies at most its prescribed finite horizon. -/
theorem solution (n m : ℕ) :
    (m : ℝ) *
      (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) ≤
        (n : ℝ) := by
  have hd : 0 < (m : ℝ) + 1 := by positivity
  have hm : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hFrac : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ hd).2
    linarith
  have hReal : (m : ℝ) * ((n : ℝ) / ((m : ℝ) + 1)) ≤ (n : ℝ) := by
    calc
      (m : ℝ) * ((n : ℝ) / ((m : ℝ) + 1)) =
        ((m : ℝ) / ((m : ℝ) + 1)) * (n : ℝ) := by ring
      _ ≤ 1 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hFrac hn
      _ = (n : ℝ) := one_mul _
  simpa only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
    NNReal.coe_one] using hReal
