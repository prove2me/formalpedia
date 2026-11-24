-- Prove2me | solution 1 for BalanceSpecification.exists_large_successive_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:58:07.928091+00:00
-- url     : https://prove2.me/submissions/178a78d4-65c6-4986-8cbc-3c5249cd1134

module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBounds

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ} (hS : ¬HasBoundedSuccessiveGaps S)
    (k : ℕ) : ∃ a ∈ S, ∃ b ∈ S, a < b ∧
      (∀ s ∈ S, a < s → b ≤ s) ∧ a + k < b := by
  unfold HasBoundedSuccessiveGaps at hS
  push Not at hS
  obtain ⟨a, ha, b, hb, hab, hconsecutive, hgap⟩ := hS k
  exact ⟨a, ha, b, hb, hab, hconsecutive, by omega⟩
end BalanceSpecification
