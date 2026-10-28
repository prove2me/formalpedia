-- Prove2me | solution 1 for FinancialDerivatives.FD05.FD04_upperBarrierTouched_iff_firstUpperHit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:42:48.88766+00:00
-- url     : https://prove2.me/submissions/07421fdd-7ddd-4b75-a7cb-28a86cdc680c

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_upperBarrierTouched
import Definitions.Def_fd05_monitoredSpots
import Definitions.Def_fd05_firstUpperHit

open FinancialDerivatives.FD03 FinancialDerivatives.FD04 FinancialDerivatives.FD05


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

theorem solution
    (m : BinomialMarket) (N : ℕ) (B : ℝ)
    (monitor : ℕ → Bool) (steps : List Bool) :
    upperBarrierTouched B (monitoredSpots m N monitor steps) = true ↔
      firstUpperHit m N B monitor steps ≤ N := by
  unfold firstUpperHit upperBarrierTouched monitoredSpots
  rw [A3FD_headD_le _ _ (A3FD_filter_le _ _), ne_eq, List.filter_eq_nil_iff]
  simp only [List.any_eq_true, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq,
    Bool.and_eq_true, not_forall, not_and, not_le, exists_prop]
  constructor
  · rintro ⟨_, ⟨t, ⟨ht, hm⟩, rfl⟩, hB⟩
    exact ⟨t, ht, hm, not_lt.mpr hB⟩
  · rintro ⟨t, ht, hm, hB⟩
    exact ⟨_, ⟨t, ⟨ht, hm⟩, rfl⟩, not_lt.mp hB⟩
