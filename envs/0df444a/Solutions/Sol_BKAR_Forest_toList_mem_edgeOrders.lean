-- Prove2me | solution 1 for BKAR.Forest.toList_mem_edgeOrders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:03.916113+00:00
-- url     : https://prove2.me/submissions/14749d93-90df-47dc-b9d8-63b78f02b270

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_mem_edgeOrders_iff

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) :
    F.edges.toList ∈ F.edgeOrders :=
  (F.mem_edgeOrders_iff).mpr (List.Perm.refl _)
end BKAR.Forest
