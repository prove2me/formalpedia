-- Prove2me | solution 1 for GallaiEdmonds.tb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:47.476546+00:00
-- url     : https://prove2.me/submissions/adca67ca-65d7-43d1-ac5b-ccd79f72ecef

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Theorems.Thm_GallaiEdmonds_ncard_verts_eq_two_mul
public import Theorems.Thm_BergeMatching_two_mul_card_add_le
public import Theorems.Thm_GallaiEdmonds_oddCount_eq


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {M : G.Subgraph} (hM : M.IsMatching) (U : Set V) :
    M.verts.ncard + oddC G Uᶜ ≤ Nat.card V + U.ncard := by
  rw [ncard_verts_eq_two_mul hM, ← oddCount_eq]
  exact BergeMatching.two_mul_card_add_le hM U
end GallaiEdmonds
