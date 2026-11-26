-- Prove2me | solution 1 for GallaiEdmonds.cc_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:50.9103+00:00
-- url     : https://prove2.me/submissions/970cacc0-ae29-4854-8d15-07cf2d424ec8

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
theorem _root_.solution (h : y ∈ cc G W x) : x ∈ cc G W y := by
  obtain ⟨hx, hy, r⟩ := h; exact ⟨hy, hx, r.symm⟩
end GallaiEdmonds
