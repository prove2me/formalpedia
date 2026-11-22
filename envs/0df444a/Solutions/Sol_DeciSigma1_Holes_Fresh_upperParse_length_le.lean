-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.upperParse_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:41.522924+00:00
-- url     : https://prove2.me/submissions/cdf86611-cb37-458a-8937-2b7c2a649a97

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Bound
public import Theorems.Thm_DeciSigma1_Holes_Fresh_edge_length_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_card_mul_of_gaps
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
theorem _root_.solution (hsl : IsMinimalFresh T W) {t : ℕ} (ht : t ≤ topLevel W)
    {Z : List (List α)} (hZ : Z ∈ upperParses W t) :
    Z.length ≤ ((upperParses W t).card + 2) * edgeLengthBound k (Fintype.card S) := by
  have h := le_card_mul_of_gaps (trieNodes W t Z) (edgeLengthBound k (Fintype.card S))
    (mem_insert_self _ _) (fun a _ b hb hab hgap =>
      edge_length_le hsl ht ⟨Z, hZ, a, b, hb, hab, hgap⟩)
    Z.length (mem_insert_of_mem (mem_insert_self _ _))
  have hcard : (trieNodes W t Z).card ≤ (upperParses W t).card + 2 := by
    have h1 := card_insert_le 0 (insert Z.length ((upperParses W t).image (commonSuffixLength Z)))
    have h2 := card_insert_le Z.length ((upperParses W t).image (commonSuffixLength Z))
    have h3 := card_image_le (s := upperParses W t) (f := commonSuffixLength Z)
    unfold trieNodes; omega
  exact h.trans (Nat.mul_le_mul_right _ hcard)
end DeciSigma1.Holes.Fresh
