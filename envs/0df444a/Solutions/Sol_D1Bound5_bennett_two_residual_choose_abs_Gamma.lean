-- Prove2me | solution 1 for D1Bound5.bennett_two_residual_choose_abs_Gamma
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:16.097288+00:00
-- url     : https://prove2.me/submissions/0a648bed-a083-433f-8f7c-1bee3973898e

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Theorems.Thm_D1Bound5_bennett_shifted_half_tail_abs_Gamma

section
open Polynomial

namespace D1Bound5













/-- The exact coefficient at degree3k in the two-anchor residual is
the beta/Gamma factor used by the manuscript. -/
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) :
    |Ring.choose ((k : ℝ) + 1 / 2) (3 * k)| =
      Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma (2 * (k : ℝ) - 1 / 2) /
        (Real.pi * Real.Gamma (3 * (k : ℝ) + 1)) := by
  have hn : k + 1 + (2 * k - 1) = 3 * k := by omega
  have hm : (((2 * k - 1 : ℕ) : ℝ) + 1 / 2) = 2 * (k : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    push_cast
    ring
  have h := bennett_shifted_half_tail_abs_Gamma k (2 * k - 1)
  rw [hn, hm] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

end D1Bound5
end
