-- Prove2me | solution 1 for GallaiEdmonds.mem_cc_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:04.810716+00:00
-- url     : https://prove2.me/submissions/cd1ee885-dd75-4392-853e-5c1bf1fc05b7

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
theorem _root_.solution (hx : x ∈ W) : x ∈ cc G W x := ⟨hx, hx, Reachable.refl _⟩
end GallaiEdmonds
