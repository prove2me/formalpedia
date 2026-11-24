-- Prove2me | solution 1 for BalanceSpecification.hasBoundedSuccessiveGaps_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:58.285178+00:00
-- url     : https://prove2.me/submissions/aa436562-b725-4630-96b0-2ee727846fbe

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
theorem _root_.solution {S : Set ℕ} (hS : S.Finite) :
    HasBoundedSuccessiveGaps S := by
  obtain ⟨N, hN⟩ := hS.bddAbove
  refine ⟨N, ?_⟩
  intro a ha b hb _ _
  have hbN := hN hb
  omega
end BalanceSpecification
