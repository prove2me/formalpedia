-- Prove2me | solution 1 for GallaiEdmonds.even_ncard_verts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:29.546768+00:00
-- url     : https://prove2.me/submissions/bcfea53a-feab-4a99-bf27-27b7cbd05ad2

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Theorems.Thm_GallaiEdmonds_ncard_verts_eq_two_mul

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {M : G.Subgraph} (hM : M.IsMatching) :
    Even M.verts.ncard := by
  rw [ncard_verts_eq_two_mul hM]; exact even_two_mul _
end GallaiEdmonds
