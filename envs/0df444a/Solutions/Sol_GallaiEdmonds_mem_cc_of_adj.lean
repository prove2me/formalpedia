-- Prove2me | solution 1 for GallaiEdmonds.mem_cc_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:26.325913+00:00
-- url     : https://prove2.me/submissions/fac73f80-891f-4585-b07d-5db6458c41ce

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
theorem _root_.solution (h : y ∈ cc G W x) (hz : z ∈ W) (hadj : G.Adj y z) : z ∈ cc G W x := by
  obtain ⟨hx, hy, r⟩ := h
  exact ⟨hx, hz, r.trans (Adj.reachable (G := G.induce W) (u := ⟨y, hy⟩) (v := ⟨z, hz⟩) hadj)⟩
end GallaiEdmonds
