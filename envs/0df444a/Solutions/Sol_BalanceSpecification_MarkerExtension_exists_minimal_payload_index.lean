-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.exists_minimal_payload_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:06.716679+00:00
-- url     : https://prove2.me/submissions/c531a7d9-ee36-4de1-b0c6-17004f92d771

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] {Y : ShiftSpace A}
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {s : ℕ → ℕ}
    (hs : ∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ s n) (l : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ l ≤ s m ∧ ∀ n : ℕ, 1 ≤ n → l ≤ s n → m ≤ n := by
  have hex := hs l
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro n hn hln
  exact Nat.find_min' hex ⟨hn, hln⟩
end BalanceSpecification.MarkerExtension
