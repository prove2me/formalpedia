-- Prove2me | solution 1 for BKAR.Forest.paramsOfOrder_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:20.719699+00:00
-- url     : https://prove2.me/submissions/c5a1d1b4-e7e8-493e-b1d9-f8f284e297c1

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_emptyParam_unique


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (order : List (Edge V)) (ts : List ℝ) :
    (Forest.empty V).paramsOfOrder order ts = emptyParam :=
  emptyParam_unique ((Forest.empty V).paramsOfOrder order ts)
end BKAR.Forest
