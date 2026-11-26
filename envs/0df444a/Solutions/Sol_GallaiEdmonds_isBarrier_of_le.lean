-- Prove2me | solution 1 for GallaiEdmonds.isBarrier_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:46.183588+00:00
-- url     : https://prove2.me/submissions/43da0e5c-1716-477c-b57f-59734484e602

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Theorems.Thm_GallaiEdmonds_tb_le


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} {M : G.Subgraph} (hM : M.IsMatching)
    (h : Nat.card V + U.ncard ≤ M.verts.ncard + oddC G Uᶜ) : IsBarrier G U :=
  ⟨M, hM, le_antisymm (tb_le hM U) h⟩
end GallaiEdmonds
