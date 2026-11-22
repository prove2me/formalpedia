-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_forall_of_card_filter_not_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:56:12.513444+00:00
-- url     : https://prove2.me/submissions/e5877395-17ab-428c-a6b3-8b03a414f2a3

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {ι κ : Type*} {R : Finset κ} {U : Finset ι}
    (p : ι → κ → Prop) [∀ u, DecidablePred (p u)] {c : ℕ}
    (hbad : ∀ u ∈ U, (R.filter fun r => ¬ p u r).card ≤ c) (hlt : U.card * c < R.card) :
    ∃ r ∈ R, ∀ u ∈ U, p u r := by
  classical
  have hU : (U.biUnion fun u => R.filter fun r => ¬ p u r).card < R.card :=
    (Finset.card_biUnion_le_card_mul _ _ _ hbad).trans_lt hlt
  obtain ⟨r, hr, hrn⟩ := Finset.exists_mem_notMem_of_card_lt_card hU
  exact ⟨r, hr, fun u hu => by_contra fun h =>
    hrn (Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨hr, h⟩⟩)⟩
end DeciSigma1.Holes.Tail
