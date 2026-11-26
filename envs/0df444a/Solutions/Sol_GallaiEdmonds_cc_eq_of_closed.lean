-- Prove2me | solution 1 for GallaiEdmonds.cc_eq_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:07.334984+00:00
-- url     : https://prove2.me/submissions/679458ea-a387-4fb0-9f6c-ee29d96b3352

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_mem_cc_self
public import Theorems.Thm_GallaiEdmonds_cc_subset
public import Theorems.Thm_GallaiEdmonds_mem_cc_of_adj
public import Theorems.Thm_GallaiEdmonds_cc_subset_of_closed
public import Theorems.Thm_GallaiEdmonds_cc_mono

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution (hW : W' ⊆ W) (hc : Closed G W W') (hx : x ∈ W') :
    cc G W' x = cc G W x := by
  refine (cc_mono hW).antisymm (cc_subset_of_closed (mem_cc_self hx) fun y hy z hz hadj => ?_)
  exact mem_cc_of_adj hy (hc y (cc_subset hy) z hz hadj) hadj
end GallaiEdmonds
