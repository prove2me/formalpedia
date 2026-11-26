-- Prove2me | solution 1 for GallaiEdmonds.tb_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:47.990306+00:00
-- url     : https://prove2.me/submissions/a253a99e-7ee4-4455-af1e-1ef269bdf62d

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Theorems.Thm_GallaiEdmonds_ncard_verts_eq_two_mul
public import Theorems.Thm_BergeMatching_exists_tutte_berge
public import Theorems.Thm_BergeMatching_two_mul_card_add_le
public import Theorems.Thm_GallaiEdmonds_oddCount_eq


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ∧
      M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard := by
  obtain ⟨M, U, hM, heq⟩ := BergeMatching.exists_tutte_berge G
  refine ⟨M, U, hM, fun M' hM' => ?_, ?_⟩
  · have := BergeMatching.two_mul_card_add_le hM' U
    omega
  · rw [ncard_verts_eq_two_mul hM, ← oddCount_eq]; exact heq
end GallaiEdmonds
