-- Prove2me | solution 1 for GallaiEdmonds.tb_restricted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:48.549231+00:00
-- url     : https://prove2.me/submissions/96e73894-02e9-4779-aa41-3fc68215bf3e

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Theorems.Thm_GallaiEdmonds_ncard_verts_eq_two_mul
public import Theorems.Thm_GallaiEdmonds_oddC_le_ncard
public import Theorems.Thm_GallaiEdmonds_oddC_congr_graph
public import Theorems.Thm_BergeMatching_exists_tutte_berge
public import Theorems.Thm_GallaiEdmonds_oddC_split
public import Theorems.Thm_GallaiEdmonds_oddCount_eq


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] (G : SimpleGraph V) (S : Set V) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N.verts ⊆ S ∧ ∃ T ⊆ S,
      S.ncard + T.ncard ≤ N.verts.ncard + oddC G (S \ T) := by
  obtain ⟨M', T0, hM', heq⟩ := BergeMatching.exists_tutte_berge (restrictG G S)
  let N : G.Subgraph :=
    { verts := M'.verts, Adj := M'.Adj, adj_sub := fun h => (M'.adj_sub h).1,
      edge_vert := M'.edge_vert, symm := M'.symm }
  have hN : N.IsMatching := fun v hv => hM' hv
  have hNS : N.verts ⊆ S := fun v hv => by
    obtain ⟨w, hw, -⟩ := hM' hv; exact (M'.adj_sub hw).2.1
  refine ⟨N, hN, hNS, T0 ∩ S, Set.inter_subset_right, ?_⟩
  rw [oddCount_eq, ← ncard_verts_eq_two_mul hM'] at heq
  have hsub : S \ T0 ⊆ T0ᶜ := fun x hx => hx.2
  have hcl : Closed (restrictG G S) T0ᶜ (S \ T0) := fun y hy z hz hadj => ⟨hadj.2.2, hz⟩
  have hsplit := oddC_split hsub hcl
  have hcongr : oddC (restrictG G S) (S \ T0) = oddC G (S \ T0) :=
    oddC_congr_graph fun a ha b hb => ⟨fun h => h.1, fun h => ⟨h, ha.1, hb.1⟩⟩
  have hle := oddC_le_ncard (restrictG G S) (T0ᶜ \ (S \ T0))
  have hST : S \ (T0 ∩ S) = S \ T0 := by
    ext x; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
  rw [hST]
  have h1 := Set.ncard_add_ncard_compl T0
  have h2 := Set.ncard_inter_add_ncard_sdiff_eq_ncard T0ᶜ (S \ T0)
  have h3 : T0ᶜ ∩ (S \ T0) = S \ T0 := Set.inter_eq_right.mpr hsub
  have h4 := Set.ncard_inter_add_ncard_sdiff_eq_ncard S T0
  have h5 : (T0 ∩ S).ncard ≤ T0.ncard := Set.ncard_le_ncard Set.inter_subset_left
  have h6 : S ∩ T0 = T0 ∩ S := Set.inter_comm _ _
  rw [h3] at h2
  rw [h6] at h4
  change M'.verts.ncard + oddC G (S \ T0) ≥ _
  omega
end GallaiEdmonds
