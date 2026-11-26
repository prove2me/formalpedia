-- Prove2me | solution 1 for BKAR.Forest.sum_edgeOrders_eq_sum_cons_of_edges_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:02.978334+00:00
-- url     : https://prove2.me/submissions/bc3a6a52-3b08-4136-ac93-2523ac2f0a29

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_sum_edgeSetOrders_eq_sum_cons_of_nonempty

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    {β : Type*} [AddCommMonoid β] (F : Forest V)
    (hF : F.edges.Nonempty) (φ : List (Edge V) → β) :
    Finset.sum F.edgeOrders (fun order => φ order) =
      Finset.sum F.edges.attach
        (fun e => Finset.sum (edgeSetOrders (F.edges.erase e.val))
          (fun order => φ (e.val :: order))) :=
  sum_edgeSetOrders_eq_sum_cons_of_nonempty hF φ
end BKAR.Forest
