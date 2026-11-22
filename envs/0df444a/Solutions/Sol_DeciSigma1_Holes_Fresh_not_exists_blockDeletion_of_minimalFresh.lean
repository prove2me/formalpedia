-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.not_exists_blockDeletion_of_minimalFresh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:01.865621+00:00
-- url     : https://prove2.me/submissions/1b75b7d8-412b-41e1-a528-27dd666f4b7b

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_freshDominates
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_totalLength_apply_lt


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (hsl : IsMinimalFresh T W)
    {t : ℕ} : ¬ Nonempty (BlockDeletion T W t) := by
  rintro ⟨m⟩
  exact (Nat.not_lt_of_ge (hsl.2 m.apply (m.freshDominates hsl.1))) m.totalLength_apply_lt
end DeciSigma1.Holes.Fresh
