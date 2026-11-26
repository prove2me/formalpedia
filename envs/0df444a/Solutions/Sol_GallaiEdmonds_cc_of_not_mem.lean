-- Prove2me | solution 1 for GallaiEdmonds.cc_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:37.493805+00:00
-- url     : https://prove2.me/submissions/60b412ac-c22b-4d9c-a2a3-ccd4e9f42acb

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
theorem _root_.solution (hx : x ∉ W) : cc G W x = ∅ := by
  ext y; exact ⟨fun h => (hx h.1).elim, fun h => h.elim⟩
end GallaiEdmonds
