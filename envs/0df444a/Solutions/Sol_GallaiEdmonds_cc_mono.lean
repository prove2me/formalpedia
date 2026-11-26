-- Prove2me | solution 1 for GallaiEdmonds.cc_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:29.8818+00:00
-- url     : https://prove2.me/submissions/86b1c526-c3d8-4e81-922a-5343de24f9b8

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_mem_cc_self
public import Theorems.Thm_GallaiEdmonds_cc_of_not_mem
public import Theorems.Thm_GallaiEdmonds_mem_cc_of_adj
public import Theorems.Thm_GallaiEdmonds_cc_subset_of_closed

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution (h : W' ⊆ W) : cc G W' x ⊆ cc G W x := by
  by_cases hx : x ∈ W'
  · exact cc_subset_of_closed (mem_cc_self (h hx)) fun y hy z hz hadj =>
      mem_cc_of_adj hy (h hz) hadj
  · rw [cc_of_not_mem hx]; exact Set.empty_subset _
end GallaiEdmonds
