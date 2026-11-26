-- Prove2me | solution 1 for GallaiEdmonds.mem_of_mem_cc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:47.084911+00:00
-- url     : https://prove2.me/submissions/fbfdacf4-9518-4b40-ae34-ed78f75cf4be

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
theorem _root_.solution (h : y ∈ cc G W x) : x ∈ W := h.1
end GallaiEdmonds
