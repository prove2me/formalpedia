-- Prove2me | solution 1 for BergeTheorem.two_mul_card_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:09.739374+00:00
-- url     : https://prove2.me/submissions/1a6fa018-eea3-4db7-b558-4751030eb41e

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_BergeMatching_two_mul_card_add_le


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeTheorem
variable {V : Type*}
namespace BergeTheorem
theorem _root_.solution [Finite V] {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching)
    (U : Set V) : 2 * M.edgeSet.ncard + oddCount G U ≤ Nat.card V + U.ncard :=
  BergeMatching.two_mul_card_add_le hM U
end BergeTheorem
