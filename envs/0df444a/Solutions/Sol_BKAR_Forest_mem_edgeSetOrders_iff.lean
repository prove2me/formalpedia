-- Prove2me | solution 1 for BKAR.Forest.mem_edgeSetOrders_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:13.308517+00:00
-- url     : https://prove2.me/submissions/c967bd08-0f3e-4b02-bc8f-25f553b48155

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
theorem _root_.solution (S : Finset (Edge V))
    {order : List (Edge V)} :
    order ∈ edgeSetOrders S ↔ order.Perm S.toList := by
  rw [edgeSetOrders, List.mem_toFinset, List.mem_permutations]
end BKAR.Forest
