-- Prove2me | solution 1 for FinancialDerivatives.FD05.firstUpperHit_no_hit_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:42:01.661016+00:00
-- url     : https://prove2.me/submissions/4e4b9f43-7ba7-4103-b30e-968f93af9e77

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_firstUpperHit
import Definitions.Def_fd05_historySpot

open FinancialDerivatives.FD03 FinancialDerivatives.FD05


theorem A3FD_headD_eq (l : List ℕ) (N : ℕ) (hl : ∀ x ∈ l, x ≤ N) :
    l.headD (N + 1) = N + 1 ↔ l = [] := by
  cases l with
  | nil => simp
  | cons a l =>
    have := hl a (List.mem_cons_self ..)
    simp only [List.headD_cons, reduceCtorEq, iff_false]
    omega

theorem A3FD_headD_le (l : List ℕ) (N : ℕ) (hl : ∀ x ∈ l, x ≤ N) :
    l.headD (N + 1) ≤ N ↔ l ≠ [] := by
  cases l with
  | nil => simp
  | cons a l =>
    have := hl a (List.mem_cons_self ..)
    simp only [List.headD_cons, ne_eq, reduceCtorEq, not_false_eq_true, iff_true]
    exact this

theorem A3FD_filter_le (N : ℕ) (p : ℕ → Bool) :
    ∀ x ∈ (List.range (N + 1)).filter p, x ≤ N := by
  intro x hx
  have := (List.mem_filter.mp hx).1
  rw [List.mem_range] at this
  omega

theorem solution (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (steps : List Bool) :
    firstUpperHit m N B monitor steps = N + 1 ↔
      ∀ t : ℕ, t ≤ N → monitor t = true →
        historySpot m (steps.take t) < B := by
  unfold firstUpperHit
  rw [A3FD_headD_eq _ _ (A3FD_filter_le _ _), List.filter_eq_nil_iff]
  simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq, not_and, not_le]
  constructor
  · intro h t ht hm
    exact h t (by omega) hm
  · intro h t ht hm
    exact h t (by omega) hm
