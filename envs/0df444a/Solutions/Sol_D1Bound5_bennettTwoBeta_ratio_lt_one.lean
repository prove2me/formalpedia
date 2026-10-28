-- Prove2me | solution 1 for D1Bound5.bennettTwoBeta_ratio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:19:53.672228+00:00
-- url     : https://prove2.me/submissions/9a4eb918-4e78-4c9f-86f0-3424ded7a89d

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5













/-- The rational recurrence factor is strictly below one at every positive order. -/
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) :
    (((27 / 4 : ℝ) * ((k : ℝ) + 3 / 2) * (2 * (k : ℝ) - 1 / 2) *
      (2 * (k : ℝ) + 1 / 2)) /
        ((3 * (k : ℝ) + 1) * (3 * (k : ℝ) + 2) * (3 * (k : ℝ) + 3))) < 1 := by
  have hden : 0 < (3 * (k : ℝ) + 1) * (3 * (k : ℝ) + 2) * (3 * (k : ℝ) + 3) := by
    positivity
  apply (div_lt_one hden).mpr
  have hdiff :
      (3 * (k : ℝ) + 1) * (3 * (k : ℝ) + 2) * (3 * (k : ℝ) + 3) -
        (27 / 4 : ℝ) * ((k : ℝ) + 3 / 2) * (2 * (k : ℝ) - 1 / 2) *
          (2 * (k : ℝ) + 1 / 2) =
      (432 * (k : ℝ) ^ 2 + 1110 * (k : ℝ) + 273) / 32 := by ring
  have hp : 0 < (432 * (k : ℝ) ^ 2 + 1110 * (k : ℝ) + 273) / 32 := by positivity
  linarith







end D1Bound5
end
