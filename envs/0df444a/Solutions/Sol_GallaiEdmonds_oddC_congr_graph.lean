-- Prove2me | solution 1 for GallaiEdmonds.oddC_congr_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:06.028918+00:00
-- url     : https://prove2.me/submissions/c4375842-17a1-404a-8eb3-75734165fe95

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Theorems.Thm_GallaiEdmonds_cc_congr_graph


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution {H : SimpleGraph V} {W : Set V}
    (h : ∀ a ∈ W, ∀ b ∈ W, H.Adj a b ↔ G.Adj a b) : oddC H W = oddC G W := by
  have : oddComps H W = oddComps G W := by
    ext K
    simp only [oddComps, comps, cc_congr_graph h]
  rw [oddC, oddC, this]
end GallaiEdmonds
