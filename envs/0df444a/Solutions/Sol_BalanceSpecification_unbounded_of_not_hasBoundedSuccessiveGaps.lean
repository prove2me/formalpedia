-- Prove2me | solution 1 for BalanceSpecification.unbounded_of_not_hasBoundedSuccessiveGaps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:01.282936+00:00
-- url     : https://prove2.me/submissions/d2f3a21a-aded-4b97-99c1-73cd93e90b7d

module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Theorems.Thm_BalanceSpecification_exists_large_successive_gap

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ}
    (hS : ¬HasBoundedSuccessiveGaps S) : ∀ k : ℕ, ∃ b ∈ S, k < b := by
  intro k
  obtain ⟨a, ha, b, hb, hab, hconsecutive, hgap⟩ := exists_large_successive_gap hS k
  exact ⟨b, hb, by omega⟩
end BalanceSpecification
