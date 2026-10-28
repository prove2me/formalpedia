-- Prove2me | solution 1 for D1Bound5.bennett_two_coefficient_rounding
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:57:00.34322+00:00
-- url     : https://prove2.me/submissions/c00466c0-e9ba-4174-bafd-a67b955cf251

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5







/-- The small loss from the degree-(k+1) numerator majorant fits strictly
inside the manuscript's rounding of the exponential base to 42. -/
theorem _root_.solution (T : ℝ) (hT : 1000 ≤ T) :
    ((1 + 7 / (5 * T)) / (1 - 1 / T)) *
      ((125 / 3 : ℝ) * (1 + 7 / (5 * T))) < 42 := by
  have hT0 : 0 < T := by linarith
  have hη : 0 < 1 - 1 / T := by
    have hdiv : 1 / T < 1 := (div_lt_one hT0).mpr (by linarith)
    linarith
  have hF0 : 0 ≤ 1 + 7 / (5 * T) := by positivity
  have hF : 1 + 7 / (5 * T) ≤ 5007 / 5000 := by
    have hdiv : 7 / (5 * T) ≤ 7 / 5000 := by
      apply (div_le_div_iff₀ (by positivity : 0 < 5 * T) (by norm_num : (0 : ℝ) < 5000)).mpr
      nlinarith
    linarith
  have hηlow : 999 / 1000 ≤ 1 - 1 / T := by
    have hdiv : 1 / T ≤ 1 / 1000 := by
      apply (div_le_div_iff₀ hT0 (by norm_num : (0 : ℝ) < 1000)).mpr
      nlinarith
    linarith
  have hratio : (1 + 7 / (5 * T)) / (1 - 1 / T) ≤ 1669 / 1665 := by
    apply (div_le_iff₀ hη).mpr
    nlinarith
  calc
    _ ≤ (1669 / 1665 : ℝ) * ((125 / 3) * (5007 / 5000)) := by
      apply mul_le_mul hratio
        (mul_le_mul_of_nonneg_left hF (by norm_num))
        (mul_nonneg (by norm_num) hF0) (by norm_num)
    _ < 42 := by norm_num



end D1Bound5
end
