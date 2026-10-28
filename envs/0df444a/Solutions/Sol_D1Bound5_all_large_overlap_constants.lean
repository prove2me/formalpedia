-- Prove2me | solution 1 for D1Bound5.all_large_overlap_constants
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:21.470755+00:00
-- url     : https://prove2.me/submissions/448765d5-456a-4197-9392-4d0d5f30e8ea

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

section
namespace D1Bound5

private theorem allLargeMonomial_lower_bound
    (A B S : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B) (hS : 3 ≤ S)
    (c L : ℝ) (p q r : ℕ) (hc : 0 ≤ c)
    (hnum : L < c * (3 : ℝ) ^ (p + q + r)) :
    L < c * (A ^ p * B ^ q * S ^ r) := by
  have hprod : (3 : ℝ) ^ p * 3 ^ q * 3 ^ r ≤ A ^ p * B ^ q * S ^ r := by
    gcongr <;> first | assumption | norm_num
  have hn : L < c * ((3 : ℝ) ^ p * 3 ^ q * 3 ^ r) := by
    simpa only [pow_add] using hnum
  exact hn.trans_le (mul_le_mul_of_nonneg_left hprod hc)

/-- All fifteen sufficient overlap quotients in the no-small-entry branch,
followed by the ordinary-tail ratio. The order is precisely Table pr-overlaps
of the manuscript. Expressions are written as a positive rational coefficient
times a monomial so that monotonicity in A,B,S is explicit. No tuple growth,
interval exclusion, or main theorem is assumed in this numerical certificate. -/
theorem _root_.solution
    (A B S : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B) (hS : 3 ≤ S) :
    (13 / 10 : ℝ) <
      (1024 * (1 - 1 / 4000) / 12100) * (A ^ 10 * B ^ 10 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (256 / (36 * 243 ^ 2 * (4001 / 3999))) * (A ^ 8 * B ^ 0 * S ^ 4) ∧
    (13 / 10 : ℝ) <
      (400 ^ 2 / (16 * (5 / 4) ^ 2 * 2400 ^ 2 * (4001 / 3999))) *
        (A ^ 20 * B ^ 4 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 2 / (16 * (5 / 4) ^ 2 * 2400 ^ 2 * (4001 / 3999))) *
        (A ^ 20 * B ^ 0 * S ^ 2) ∧
    (13 / 10 : ℝ) <
      (400 ^ 2 / (16 * 3 ^ 2 * 4143 ^ 2 * (4001 / 3999))) *
        (A ^ 20 * B ^ 0 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 2 / (16 * 3 ^ 2 * 2265 ^ 2 * (4001 / 3999))) *
        (A ^ 20 * B ^ 0 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 4 / (16 * (35 / 16) ^ 2 * ((8 / 9) * 608 ^ 2) ^ 2 * (4001 / 3999))) *
        (A ^ 36 * B ^ 0 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 4 / (16 * (3920 / 81) ^ 2 * 4143 ^ 2 * (4001 / 3999))) *
        (A ^ 34 * B ^ 2 * S ^ 2) ∧
    (13 / 10 : ℝ) <
      (400 ^ 2 / (16 * (35 / 32) ^ 2 * 165763 ^ 2 * (4001 / 3999))) *
        (A ^ 22 * B ^ 4 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 4 / (16 * (35 / 32) ^ 2 * 4143 ^ 2 * (4001 / 3999))) *
        (A ^ 36 * B ^ 8 * S ^ 0) ∧
    (7 / 5 : ℝ) <
      ((400 / (35 / 32)) ^ 2 / (16 * 165763 ^ 2 * (4001 / 3999))) *
        (A ^ 14 * B ^ 0 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 4 / (144 * (63 / 8) ^ 2 * 42 ^ 8 * (4001 / 3999))) *
        (A ^ 38 * B ^ 2 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 4 / (4 * 3113013 ^ 2 * (5 / 2) ^ 8 * (4001 / 3999))) *
        (A ^ 36 * B ^ 0 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 6 / (144 * (495 / 64) ^ 2 * 42 ^ 10 * (4001 / 3999))) *
        (A ^ 54 * B ^ 10 * S ^ 0) ∧
    (13 / 10 : ℝ) <
      (400 ^ 6 / (36 * 42 ^ 12 * (5 / 2) ^ 10 * (4001 / 3999))) *
        (A ^ 52 * B ^ 4 * S ^ 0) ∧
    (13 / 10 : ℝ) < (400 / 105) * (A ^ 8 * B ^ 1 * S ^ 3) := by
  repeat' constructor
  all_goals
    apply allLargeMonomial_lower_bound A B S hA hB hS
    · norm_num
    · norm_num





end D1Bound5
end
