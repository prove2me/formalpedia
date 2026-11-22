-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.upperParse_length_le_expansionBlockCountBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:49.449601+00:00
-- url     : https://prove2.me/submissions/bcb82c2d-39eb-4185-9624-4486059ce04a

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_upperParses_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperParse_length_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_upperTexts_le_textCountBound
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
theorem _root_.solution
    (hsl : IsMinimalFresh T W)
    {t : ℕ} (ht : t ≤ topLevel W)
    {Z : List (List α)} (hZ : Z ∈ upperParses W t) :
    Z.length ≤ expansionBlockCountBound k (Fintype.card S) := by
  have hseq := (card_upperParses_le hsl.1 t).trans
    (Nat.mul_le_mul_right _ (card_upperTexts_le_textCountBound hsl ht))
  exact (upperParse_length_le hsl ht hZ).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hseq 2))
end DeciSigma1.Holes.Fresh
