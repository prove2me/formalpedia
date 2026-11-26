-- Prove2me | solution 1 for BKAR.Forest.card_edgeSetOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:25:33.40543+00:00
-- url     : https://prove2.me/submissions/f6f58b0c-8cca-48a0-b4b5-1bd002837703

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution (S : Finset (Edge V)) :
    (edgeSetOrders S).card = S.card.factorial := by
  rw [edgeSetOrders]
  rw [List.toFinset_card_of_nodup]
  · rw [List.length_permutations, Finset.length_toList]
  · exact List.nodup_permutations S.toList (Finset.nodup_toList S)
end BKAR.Forest
