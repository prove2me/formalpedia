-- Prove2me | solution 1 for EulerMascheroni.P2.factorial_binomial_truncation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T19:06:44.23551+00:00
-- url     : https://prove2.me/submissions/0960665a-ff64-4829-9a40-606f33e6cda7

import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace FactorialTruncation

lemma truncate (c : ℕ → ℕ) (M J q : ℕ) (h : q ∣ J.factorial) :
    (∑ j ∈ Finset.range M, j.factorial * c j) ≡
      (∑ j ∈ Finset.range (min M J), j.factorial * c j) [MOD q] := by
  induction M with
  | zero => simp [Nat.ModEq]
  | succ M ih =>
    by_cases hm : M < J
    · rw [min_eq_left (Nat.succ_le_of_lt hm)]
    · have hJM : J ≤ M := le_of_not_gt hm
      have hd : q ∣ M.factorial * c M :=
        dvd_mul_of_dvd_left (h.trans (Nat.factorial_dvd_factorial hJM)) _
      have hz : M.factorial * c M ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr hd
      simpa only [Finset.sum_range_succ, min_eq_right hJM,
        min_eq_right (hJM.trans (Nat.le_succ M)), add_zero] using ih.add hz

end FactorialTruncation

theorem solution (n q J : ℕ) (h : q ∣ J.factorial) :
    (∑ j ∈ Finset.range (n+1),
      j.factorial * (n.choose j)^3 * ((2*n-j).choose n)^2) ≡
    (∑ j ∈ Finset.range (min (n+1) J),
      j.factorial * (n.choose j)^3 * ((2*n-j).choose n)^2) [MOD q] := by
  simpa only [mul_assoc] using FactorialTruncation.truncate
    (fun j => (n.choose j)^3 * ((2*n-j).choose n)^2) (n+1) J q h

#print axioms solution
