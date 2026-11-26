-- Prove2me | solution 1 for GallaiEdmonds.oddC_le_ncard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:45.308294+00:00
-- url     : https://prove2.me/submissions/a52a1e45-9d1b-4b29-90ba-5426b9d18623

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] (H : SimpleGraph V) (W : Set V) : oddC H W ≤ W.ncard := by
  have hsub : oddComps H W ⊆ cc H W '' W := by
    rintro K ⟨⟨x, hx, rfl⟩, -⟩; exact ⟨x, hx, rfl⟩
  exact (Set.ncard_le_ncard hsub).trans (Set.ncard_image_le)
end GallaiEdmonds
