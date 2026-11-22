-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.card_upperTexts_le_textCountBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:11.236682+00:00
-- url     : https://prove2.me/submissions/1e33ad36-cb07-4dd2-9b07-81c24ad195e8

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_textCountBoundAtDepth_mono
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_upperTexts_le_textCountBoundAtDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_topLevel_le
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
variable {S : Type} [Fintype S] [DecidableEq S] {T : Table α S k}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (hsl : IsMinimalFresh T W) {t : ℕ} (ht : t ≤ topLevel W) :
    (upperTexts W t).card ≤ textCountBound k (Fintype.card S) := by
  have h := card_upperTexts_le_textCountBoundAtDepth hsl (topLevel W - t) t (by omega)
  have hn := (topLevel_le hsl.1).trans (Nat.mul_le_mul_left k (Nat.sub_le (Fintype.card S) 1))
  exact h.trans (textCountBoundAtDepth_mono k (Fintype.card S) (by omega))
end DeciSigma1.Holes.Fresh
