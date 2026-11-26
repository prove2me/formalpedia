-- Prove2me | solution 1 for GallaiEdmonds.image_supp_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:13.131534+00:00
-- url     : https://prove2.me/submissions/51c2f5e1-d839-4c8f-86ee-7bdf84928b12

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution (H : SimpleGraph V) (W : Set V) (a : W) :
    Subtype.val '' ((H.induce W).connectedComponentMk a).supp = cc H W a.1 := by
  ext y
  simp only [Set.mem_image, ConnectedComponent.mem_supp_iff,
    ConnectedComponent.eq]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨a.2, b.2, hb.symm⟩
  · rintro ⟨_, hy, r⟩; exact ⟨⟨y, hy⟩, r.symm, rfl⟩
end GallaiEdmonds
