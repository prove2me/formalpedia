-- Prove2me | solution 1 for GallaiEdmonds.oddComps_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:05:13.473985+00:00
-- url     : https://prove2.me/submissions/d810aad8-ca5c-46e3-884a-98ebbfa68d19

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_comps_self

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution {K : Set V} (hK : K ∈ comps G W) (hodd : Odd K.ncard) :
    oddComps G K = {K} := by
  ext K'
  simp only [oddComps, comps_self hK, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, hodd⟩
end GallaiEdmonds
