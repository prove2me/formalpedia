-- Prove2me | solution 1 for GallaiEdmonds.comps_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:23.504556+00:00
-- url     : https://prove2.me/submissions/70472799-1caa-42b9-a579-5dff3d3bf141

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_cc_subset
public import Theorems.Thm_GallaiEdmonds_cc_eq_of_closed
public import Theorems.Thm_GallaiEdmonds_cc_mem_comps
public import Theorems.Thm_GallaiEdmonds_comps_nonempty
public import Theorems.Thm_GallaiEdmonds_comps_eq_cc

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution (hW : W' ⊆ W) (hc : Closed G W W') :
    comps G W' = {K | K ∈ comps G W ∧ K ⊆ W'} := by
  ext K; constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by rw [cc_eq_of_closed hW hc hx]; exact cc_mem_comps (hW hx), cc_subset⟩
  · rintro ⟨hK, hKW'⟩
    obtain ⟨x, hx⟩ := comps_nonempty hK
    refine ⟨x, hKW' hx, ?_⟩
    rw [cc_eq_of_closed hW hc (hKW' hx), comps_eq_cc hK hx]
end GallaiEdmonds
