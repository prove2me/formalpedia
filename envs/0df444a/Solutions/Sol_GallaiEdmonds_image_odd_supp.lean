-- Prove2me | solution 1 for GallaiEdmonds.image_odd_supp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:03:07.467044+00:00
-- url     : https://prove2.me/submissions/30835bfc-cbd5-4e40-a927-e8290e3d49b4

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
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
    (fun c : (H.induce W).ConnectedComponent => Subtype.val '' c.supp) ''
      (H.induce W).oddComponents = oddComps H W := by
  ext K; constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← image_univ_supp]; exact ⟨c, Set.mem_univ _, rfl⟩
    · rw [Set.ncard_image_of_injective _ Subtype.val_injective]; exact hc
  · rintro ⟨hK, hodd⟩
    rw [← image_univ_supp] at hK
    obtain ⟨c, -, rfl⟩ := hK
    refine ⟨c, ?_, rfl⟩
    rw [Set.ncard_image_of_injective _ Subtype.val_injective] at hodd
    exact hodd
end GallaiEdmonds
