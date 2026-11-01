-- Prove2me | solution 1 for BudgetAgg.NashChar.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:50:35.620198+00:00
-- url     : https://prove2.me/submissions/fd77153d-0131-4d93-aac7-72e46181073d

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Theorems.Thm_BudgetAgg_NashChar_proposition_1
import Theorems.Thm_BudgetAgg_NashChar_proposition_2
import Theorems.Thm_BudgetAgg_NashChar_nash_efficient_gsp
import Theorems.Thm_BudgetAgg_NashChar_theorem_3_uniqueness

open BudgetAgg.NashChar

theorem solution {n m : ℕ} [NeZero n] [NeZero m] (f : Mechanism n m) :
    (Continuous f ∧ IsGroupSP f ∧ ∀ P, IsCoreFairShare P (f P)) ↔
      (∀ P, IsNashOutcome P (f P).1) := by
  constructor
  · rintro ⟨hc, hg, hcore⟩
    exact theorem_3_uniqueness f hc hg hcore
  · intro h
    exact ⟨proposition_1 f h, (nash_efficient_gsp f h).2,
      fun P => proposition_2 P (f P) (h P)⟩

