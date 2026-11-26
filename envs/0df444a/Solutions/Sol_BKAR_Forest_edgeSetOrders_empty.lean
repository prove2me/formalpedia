-- Prove2me | solution 1 for BKAR.Forest.edgeSetOrders_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:02:17.920825+00:00
-- url     : https://prove2.me/submissions/31eabf4d-e7a6-408a-8bb4-08262935b141

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
theorem _root_.solution :
    edgeSetOrders (∅ : Finset (Edge V)) = {[]} := by
  rw [edgeSetOrders, Finset.toList_empty, List.permutations_nil]
  rfl
end BKAR.Forest
