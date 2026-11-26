-- Prove2me | solution 1 for GallaiEdmonds.IsBarrier.eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:45.405126+00:00
-- url     : https://prove2.me/submissions/a20f0be2-f735-474e-8938-559476c8afaa

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Theorems.Thm_GallaiEdmonds_verts_le_of_max
public import Theorems.Thm_GallaiEdmonds_tb_le


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
namespace IsBarrier
theorem _root_.solution [Finite V] {U : Set V} (hU : IsBarrier G U) {M : G.Subgraph}
    (hM : M.IsMatching)
    (hmax : ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M.verts.ncard + oddC G Uᶜ = Nat.card V + U.ncard := by
  obtain ⟨M0, hM0, h0⟩ := hU
  have := verts_le_of_max hM0 hM hmax
  have := tb_le hM U
  omega
end IsBarrier
end GallaiEdmonds
