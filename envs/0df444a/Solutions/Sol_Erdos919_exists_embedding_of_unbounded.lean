-- Prove2me | solution 1 for Erdos919.exists_embedding_of_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:37:21.70716+00:00
-- url     : https://prove2.me/submissions/23d84a73-4492-4b7b-9826-1de18264defd

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_le_aleph1_of_lt_aleph2
public import Theorems.Thm_Erdos919_exists_gt_of_small

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution (U : Set W.{u}) (hU : ∀ x, ∃ u ∈ U, x ≤ u) :
    Nonempty (W.{u} ↪o U) := by
  have hcard : ℵ_ 2 ≤ #U := by
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := exists_gt_of_small (J := U) Subtype.val (le_aleph1_of_lt_aleph2 h)
    obtain ⟨u, hu, hvu⟩ := hU v
    exact absurd (hv ⟨u, hu⟩) (not_lt.2 hvu)
  have htype : typeLT W.{u} ≤ typeLT U := by
    rw [type_toType]
    calc (ℵ_ 2 : Cardinal.{u}).ord ≤ (#U).ord := ord_le_ord.2 hcard
      _ = (typeLT U).card.ord := by rw [card_type]
      _ ≤ typeLT U := ord_card_le _
  obtain ⟨f⟩ := type_le_iff'.1 htype
  exact ⟨OrderEmbedding.ofStrictMono f (fun a b h => f.map_rel_iff.2 h)⟩
end Erdos919
