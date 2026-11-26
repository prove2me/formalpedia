-- Prove2me | solution 1 for GallaiEdmonds.natCard_components_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:03:21.96102+00:00
-- url     : https://prove2.me/submissions/bc5214d4-d8e7-44e1-a65d-ef38ac5d2f15

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_image_supp_injective
public import Theorems.Thm_GallaiEdmonds_image_univ_supp

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] (H : SimpleGraph V) (W : Set V) :
    Nat.card (H.induce W).ConnectedComponent = (comps H W).ncard := by
  rw [← image_univ_supp, Set.ncard_image_of_injective _ (image_supp_injective H W),
    Set.ncard_univ]
end GallaiEdmonds
