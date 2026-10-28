-- Prove2me | solution 1 for D1Bound5.negative_binomial_positive_tail_tsum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:34.456735+00:00
-- url     : https://prove2.me/submissions/b30a47a5-a472-4482-9440-09ead4d8fb75

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset

namespace D1Bound5

/-- Exact positive-degree tail of a negative-binomial generating function. -/
theorem _root_.solution (q : ℕ) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' j : ℕ, (Nat.choose (j + 1 + q) q : ℝ) * r ^ (j + 1)) =
      1 / (1 - r) ^ (q + 1) - 1 := by
  have hr : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hh := hasSum_choose_mul_geometric_of_norm_lt_one q hr
  have hsplit := hh.summable.tsum_eq_zero_add
  simp only [Nat.zero_add, Nat.choose_self, Nat.cast_one, pow_zero, mul_one] at hsplit
  rw [hh.tsum_eq] at hsplit
  linarith



end D1Bound5
end
