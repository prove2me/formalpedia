-- Prove2me | solution 1 for GallaiEdmonds.verts_le_of_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:11.559562+00:00
-- url     : https://prove2.me/submissions/4e87069c-0fe9-40fb-987e-9ec85987349c

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Theorems.Thm_GallaiEdmonds_ncard_verts_eq_two_mul


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {M M' : G.Subgraph} (hM' : M'.IsMatching) (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M'.verts.ncard ≤ M.verts.ncard := by
  rw [ncard_verts_eq_two_mul hM', ncard_verts_eq_two_mul hM]
  have := hmax M' hM'
  omega
end GallaiEdmonds
