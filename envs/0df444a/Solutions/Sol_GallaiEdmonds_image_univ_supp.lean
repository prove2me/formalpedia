-- Prove2me | solution 1 for GallaiEdmonds.image_univ_supp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:32.887873+00:00
-- url     : https://prove2.me/submissions/7e5bfe12-5ac8-4ed1-96bd-415d372d0a2d

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_image_supp_mk

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution (H : SimpleGraph V) (W : Set V) :
    (fun c : (H.induce W).ConnectedComponent => Subtype.val '' c.supp) '' Set.univ =
      comps H W := by
  ext K; constructor
  · rintro ⟨c, -, rfl⟩
    induction c using ConnectedComponent.ind with
    | h a => exact ⟨a.1, a.2, image_supp_mk H W a⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, Set.mem_univ _, image_supp_mk H W ⟨x, hx⟩⟩
end GallaiEdmonds
