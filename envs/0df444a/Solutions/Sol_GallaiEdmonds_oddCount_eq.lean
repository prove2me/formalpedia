-- Prove2me | solution 1 for GallaiEdmonds.oddCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:00.447389+00:00
-- url     : https://prove2.me/submissions/e4e1fcee-9ecb-40a7-9390-21c3e66180fe

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_oddComponents_ncard_eq

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] (H : SimpleGraph V) (U : Set V) :
    BergeMatching.oddCount H U = oddC H Uᶜ := by
  have h : (⊤ : H.Subgraph).deleteVerts U = (⊤ : H.Subgraph).induce Uᶜ := by
    ext a b
    · simp [Set.compl_eq_univ_sdiff]
    · simp only [Subgraph.verts_top, Set.mem_univ, Subgraph.top_adj,
        true_and, Subgraph.induce_adj, Set.mem_compl_iff, Set.mem_sdiff]
  have e := induce_eq_coe_induce_top (G := H) Uᶜ
  rw [BergeMatching.oddCount, h]
  exact (congrArg (fun K : SimpleGraph (Uᶜ : Set V) => K.oddComponents.ncard) e).symm.trans
    (oddComponents_ncard_eq H Uᶜ)
end GallaiEdmonds
