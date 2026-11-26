-- Prove2me | solution 1 for GallaiEdmonds.cc_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:28.017386+00:00
-- url     : https://prove2.me/submissions/3ee9d807-6160-4e44-bbab-8cf0ead4b54f

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
theorem _root_.solution (h : y ∈ cc G W x) : cc G W y = cc G W x := by
  obtain ⟨hx, hy, r⟩ := h
  ext z; constructor
  · rintro ⟨_, hz, r'⟩; exact ⟨hx, hz, r.trans r'⟩
  · rintro ⟨_, hz, r'⟩; exact ⟨hy, hz, r.symm.trans r'⟩
end GallaiEdmonds
