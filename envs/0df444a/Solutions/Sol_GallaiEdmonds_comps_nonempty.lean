-- Prove2me | solution 1 for GallaiEdmonds.comps_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:21.870799+00:00
-- url     : https://prove2.me/submissions/09c03524-973d-4808-abe2-e5001f3a0150

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_mem_cc_self

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution {K : Set V} (hK : K ∈ comps G W) : K.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hK; exact ⟨x, mem_cc_self hx⟩
end GallaiEdmonds
