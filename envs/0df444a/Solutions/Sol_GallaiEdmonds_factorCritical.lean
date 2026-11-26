-- Prove2me | solution 1 for GallaiEdmonds.factorCritical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:48.720518+00:00
-- url     : https://prove2.me/submissions/fa18ced4-2bd3-4df7-a8b3-6a227e49b808

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_compSet_mem_oddComps
public import Theorems.Thm_GallaiEdmonds_IsBarrier_eq
public import Theorems.Thm_GallaiEdmonds_exists_minBarrier
public import Theorems.Thm_GallaiEdmonds_step1


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] (c : (G.induce (setD G)).ConnectedComponent) :
    ∀ v ∈ compSet G c, HasPerfectMatchingOn G (compSet G c \ {v}) := by
  obtain ⟨U, hU⟩ := exists_minBarrier G
  intro v hv
  have hK := compSet_mem_oddComps G hU c
  obtain ⟨hvD, -⟩ := id hv
  obtain ⟨M, ⟨hM, hmax⟩, hvM⟩ := hvD
  obtain ⟨-, -, h1c, -⟩ := step1 hM (hU.1.eq hM hmax)
  refine ⟨M.induce (compSet G c \ {v}), ?_, rfl⟩
  intro w hw
  rcases h1c _ hK v hv w hw.1 (fun h => hw.2 h.symm) with ⟨z, -, hz⟩ | ⟨z, hzK, hz⟩
  · exact (hvM (M.edge_vert hz)).elim
  · have hzv : z ≠ v := fun h => hvM (h ▸ M.edge_vert hz.symm)
    exact ⟨z, ⟨hw, ⟨hzK, hzv⟩, hz⟩, fun z' h => hM.eq_of_adj_left h.2.2 hz⟩
end GallaiEdmonds
