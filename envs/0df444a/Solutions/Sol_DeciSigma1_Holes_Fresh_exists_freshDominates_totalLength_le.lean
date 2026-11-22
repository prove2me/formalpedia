-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.exists_freshDominates_totalLength_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:00.21302+00:00
-- url     : https://prove2.me/submissions/b87ee54e-6866-4578-be19-f5ecb5c1cb94

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_totalLength_le_freshTupleBound
public import Theorems.Thm_DeciSigma1_Readers_exists_isMinimalFresh_freshDominates


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (hW : ∀ i, T.Fresh W i) :
    ∃ U, FreshDominates T U W ∧ totalLength U ≤ freshTupleBound k (Fintype.card S) := by
  obtain ⟨U, hU, hsl⟩ := exists_isMinimalFresh_freshDominates hW
  exact ⟨U, hU, totalLength_le_freshTupleBound hsl⟩
end DeciSigma1.Holes.Fresh
