-- Prove2me | solution 1 for BergeTheorem.exists_tutte_berge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:19.861803+00:00
-- url     : https://prove2.me/submissions/9c2ffdf8-9841-4bc1-a26d-4eb54060ca5f

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_BergeMatching_exists_tutte_berge


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeTheorem
variable {V : Type*}
namespace BergeTheorem
theorem _root_.solution [Finite V] (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      2 * M.edgeSet.ncard + oddCount G U = Nat.card V + U.ncard :=
  BergeMatching.exists_tutte_berge G
end BergeTheorem
