-- Prove2me | solution 1 for GallaiEdmonds.exists_max_missing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:10:56.278477+00:00
-- url     : https://prove2.me/submissions/c7fe0768-d39b-4afd-aad2-d47f0a9313ac

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Theorems.Thm_GallaiEdmonds_hall_injection
public import Theorems.Thm_GallaiEdmonds_construct_matching
public import Theorems.Thm_GallaiEdmonds_IsBarrier_eq
public import Theorems.Thm_GallaiEdmonds_comps_eq_cc
public import Theorems.Thm_GallaiEdmonds_comps_subset
public import Theorems.Thm_GallaiEdmonds_minBarrier_factorCritical
public import Theorems.Thm_GallaiEdmonds_ncard_verts_eq_two_mul
public import Theorems.Thm_GallaiEdmonds_step1


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    {M : G.Subgraph} (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard)
    {v : V} (hv : v ∈ oddPart G U) :
    ∃ M' : G.Subgraph, M'.IsMatching ∧
      (∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M'.edgeSet.ncard) ∧ v ∉ M'.verts := by
  obtain ⟨f, hf, hfinj⟩ := hall_injection hU hM hmax hv
  have heq := hU.1.eq hM hmax
  obtain ⟨-, -, -, h1d⟩ := step1 hM heq
  have hfc : ∀ K ∈ oddComps G Uᶜ, ∀ y ∈ K, ∃ P : G.Subgraph, P.IsMatching ∧ P.verts = K \ {y} :=
    fun K hK y hy => minBarrier_factorCritical hU hM hmax hK hy
  have hev : ∀ K ∈ comps G Uᶜ, Even K.ncard → ∃ P : G.Subgraph, P.IsMatching ∧ P.verts = K := by
    intro K hK heven
    refine ⟨M.induce K, ?_, rfl⟩
    intro y hy
    have hyU : y ∉ U := comps_subset hK hy
    obtain ⟨w, hw, hadj⟩ := h1d y hyU (by rwa [← comps_eq_cc hK hy])
    rw [← comps_eq_cc hK hy] at hw
    exact ⟨w, ⟨hy, hw, hadj⟩, fun w' h => hM.eq_of_adj_left h.2.2 hadj⟩
  obtain ⟨M', hM', hvM', heq'⟩ := construct_matching hv hf hfinj hfc hev
  refine ⟨M', hM', fun N hN => ?_, hvM'⟩
  have h1 := ncard_verts_eq_two_mul hM
  have h2 := ncard_verts_eq_two_mul hM'
  have h3 := hmax N hN
  omega
end GallaiEdmonds
