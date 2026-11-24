-- Prove2me | solution 1 for BalanceSpecification.hasBoundedSuccessiveGaps_of_uniform_right_completion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:58:07.028644+00:00
-- url     : https://prove2.me/submissions/b99614a2-0ca0-41b0-bfc3-9af5d7ad2249

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
theorem _root_.solution {S : Set ℕ}
    (h : ∃ N : ℕ, ∀ t : ℕ, (∃ s ∈ S, t ≤ s) →
      ∃ s ∈ S, t ≤ s ∧ s ≤ t + N) : HasBoundedSuccessiveGaps S := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + 1, ?_⟩
  intro a ha b hb hab hconsecutive
  obtain ⟨s, hs, hats, hsb⟩ := hN (a + 1) ⟨b, hb, hab⟩
  have hbs := hconsecutive s hs (by omega)
  omega
end BalanceSpecification
