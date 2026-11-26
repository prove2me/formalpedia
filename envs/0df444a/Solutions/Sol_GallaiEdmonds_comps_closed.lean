-- Prove2me | solution 1 for GallaiEdmonds.comps_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:46.48108+00:00
-- url     : https://prove2.me/submissions/d8d2ea23-d82f-47e3-b048-c6abbbdb9f05

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_mem_cc_of_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution {K : Set V} (hK : K ∈ comps G W) : Closed G W K := by
  obtain ⟨x, -, rfl⟩ := hK
  exact fun y hy z hz hadj => mem_cc_of_adj hy hz hadj
end GallaiEdmonds
