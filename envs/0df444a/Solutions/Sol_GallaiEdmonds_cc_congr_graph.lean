-- Prove2me | solution 1 for GallaiEdmonds.cc_congr_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:32.646783+00:00
-- url     : https://prove2.me/submissions/81993139-570d-48fe-8e06-6ed1eb655514

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_mem_cc_self
public import Theorems.Thm_GallaiEdmonds_cc_subset
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
theorem _root_.solution {H : SimpleGraph V} (h : ∀ a ∈ W, ∀ b ∈ W, H.Adj a b ↔ G.Adj a b) :
    cc H W x = cc G W x := by
  by_cases hx : x ∈ W
  · refine (cc_subset_of_closed (mem_cc_self hx) fun y hy z hz hadj => ?_).antisymm
      (cc_subset_of_closed (mem_cc_self hx) fun y hy z hz hadj => ?_)
    · exact mem_cc_of_adj hy hz ((h y (cc_subset hy) z hz).1 hadj)
    · exact mem_cc_of_adj hy hz ((h y (cc_subset hy) z hz).2 hadj)
  · rw [cc_of_not_mem hx, cc_of_not_mem hx]
end GallaiEdmonds
