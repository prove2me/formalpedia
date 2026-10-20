-- Prove2me | solution 1 for AvramDividend.Classical.recordPartition_finite_cover_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:51:12.40755+00:00
-- url     : https://prove2.me/submissions/169ee165-4a96-49a7-9b29-7b5bd7e49a46

import Mathlib.MeasureTheory.Measure.Stieltjes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/- Exact finite coverage of consecutive half-open partition cells. -/
theorem solution
    (u : ℕ → ℝ) (hu : Monotone u)
    (n : ℕ) (x : ℝ) :
    (u 0 < x ∧ x ≤ u n) ↔
      ∃ i : ℕ, i < n ∧ u i < x ∧ x ≤ u (i + 1) := by
  induction n with
  | zero =>
      constructor
      · intro h
        exact False.elim ((not_lt_of_ge h.2) h.1)
      · rintro ⟨i, hi, _⟩
        exact False.elim ((Nat.not_lt_zero i) hi)
  | succ n ih =>
      constructor
      · intro h
        by_cases hxn : x ≤ u n
        · obtain ⟨i, hi, hxi, hxnext⟩ :=
            ih.mp ⟨h.1, hxn⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, hxi, hxnext⟩
        · exact ⟨n, Nat.lt_succ_self n, lt_of_not_ge hxn, h.2⟩
      · rintro ⟨i, hi, hxi, hxnext⟩
        have h0i : u 0 ≤ u i := hu (Nat.zero_le i)
        have hisucc : i + 1 ≤ n + 1 :=
          Nat.succ_le_succ (Nat.le_of_lt_succ hi)
        exact ⟨lt_of_le_of_lt h0i hxi, le_trans hxnext (hu hisucc)⟩
