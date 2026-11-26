-- Prove2me | solution 1 for BergeTheorem.isMaximum_iff_not_exists_augmenting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:09.181779+00:00
-- url     : https://prove2.me/submissions/f41fd8fa-49ab-4d6c-90a3-1e0926181af3

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_BergeMatching_isMaximum_iff_not_exists_augmenting


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeTheorem
variable {V : Type*}
namespace BergeTheorem
theorem _root_.solution [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) :
    (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ↔
      ¬ ∃ (u v : V) (p : G.Walk u v), IsAugmentingPath M p :=
  BergeMatching.isMaximum_iff_not_exists_augmenting hM
end BergeTheorem
