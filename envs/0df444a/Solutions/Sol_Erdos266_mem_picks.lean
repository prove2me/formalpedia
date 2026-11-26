-- Prove2me | solution 1 for Erdos266.mem_picks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:34:10.358354+00:00
-- url     : https://prove2.me/submissions/a1cab032-4c33-4819-9551-a5f82f087906

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
public import Theorems.Thm_Erdos266_picks_succ

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution {q : ℚ} {i : ℕ} : q ∈ picks i ↔ ∃ j < i, tSeq j = q := by
  induction i with
  | zero => simp [picks]
  | succ i ih =>
    rw [picks_succ, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
      · exact ⟨i, Nat.lt_succ_self i, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
      · exact Or.inl ⟨j, h, rfl⟩
      · exact Or.inr rfl
end Erdos266
