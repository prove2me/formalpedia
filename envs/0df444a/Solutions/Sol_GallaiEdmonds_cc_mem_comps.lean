-- Prove2me | solution 1 for GallaiEdmonds.cc_mem_comps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:33.172605+00:00
-- url     : https://prove2.me/submissions/7a7b3880-03e8-43dd-a058-01d79d97539d

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
theorem _root_.solution (hx : x ∈ W) : cc G W x ∈ comps G W := ⟨x, hx, rfl⟩
end GallaiEdmonds
