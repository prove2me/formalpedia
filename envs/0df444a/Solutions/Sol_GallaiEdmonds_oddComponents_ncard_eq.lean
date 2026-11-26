-- Prove2me | solution 1 for GallaiEdmonds.oddComponents_ncard_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:31.857358+00:00
-- url     : https://prove2.me/submissions/e40cc897-4a73-4f37-8d70-5bc2a0e93c7e

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_image_supp_injective
public import Theorems.Thm_GallaiEdmonds_image_odd_supp

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] (H : SimpleGraph V) (W : Set V) :
    (H.induce W).oddComponents.ncard = oddC H W := by
  rw [oddC, ← image_odd_supp, Set.ncard_image_of_injective _ (image_supp_injective H W)]
end GallaiEdmonds
