-- Prove2me | solution 1 for BalanceSpecification.infinite_of_not_hasBoundedSuccessiveGaps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:37.329805+00:00
-- url     : https://prove2.me/submissions/33f8e6fe-b358-4bd3-9950-6ff299995d29

module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Theorems.Thm_BalanceSpecification_unbounded_of_not_hasBoundedSuccessiveGaps

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ}
    (hS : ¬HasBoundedSuccessiveGaps S) : S.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨k, hk⟩
  obtain ⟨b, hb, hkb⟩ := unbounded_of_not_hasBoundedSuccessiveGaps hS k
  exact (not_lt_of_ge (hk hb)) hkb
end BalanceSpecification
