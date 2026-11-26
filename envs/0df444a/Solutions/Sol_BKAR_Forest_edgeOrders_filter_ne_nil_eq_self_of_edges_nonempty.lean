-- Prove2me | solution 1 for BKAR.Forest.edgeOrders_filter_ne_nil_eq_self_of_edges_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:20.812634+00:00
-- url     : https://prove2.me/submissions/bd4bfa7e-8914-47db-8715-025a0be7f5ab

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_edgeSetOrders_filter_ne_nil_eq_self_of_nonempty

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (hF : F.edges.Nonempty) :
    F.edgeOrders.filter (fun order => order ≠ []) = F.edgeOrders :=
  edgeSetOrders_filter_ne_nil_eq_self_of_nonempty hF
end BKAR.Forest
