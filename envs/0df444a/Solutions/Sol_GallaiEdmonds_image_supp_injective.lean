-- Prove2me | solution 1 for GallaiEdmonds.image_supp_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:29.9107+00:00
-- url     : https://prove2.me/submissions/beb8a535-7377-4cbd-bcbd-cddc443cf868

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
theorem _root_.solution (H : SimpleGraph V) (W : Set V) :
    Function.Injective fun c : (H.induce W).ConnectedComponent => Subtype.val '' c.supp :=
  (Set.image_injective.mpr Subtype.val_injective).comp ConnectedComponent.supp_injective
end GallaiEdmonds
