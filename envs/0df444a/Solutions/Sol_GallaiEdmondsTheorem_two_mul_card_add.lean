-- Prove2me | solution 1 for GallaiEdmondsTheorem.two_mul_card_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:16:43.326308+00:00
-- url     : https://prove2.me/submissions/1e18842e-bf5c-4dae-9c34-f93cec3dbff0

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_GallaiEdmonds_two_mul_card_add


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmondsTheorem
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmondsTheorem
theorem _root_.solution [Finite V] {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    2 * M.edgeSet.ncard + Nat.card (G.induce (setD G)).ConnectedComponent =
      Nat.card V + (setA G).ncard :=
  GallaiEdmonds.two_mul_card_add G hM
end GallaiEdmondsTheorem
