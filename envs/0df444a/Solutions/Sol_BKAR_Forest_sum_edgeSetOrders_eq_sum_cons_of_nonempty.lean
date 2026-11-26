-- Prove2me | solution 1 for BKAR.Forest.sum_edgeSetOrders_eq_sum_cons_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:09.582299+00:00
-- url     : https://prove2.me/submissions/f168031b-35a9-4eff-bfc2-95c20b7884d5

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_sum_edgeSetOrders_filter_ne_nil_eq_sum_cons
import Theorems.Thm_BKAR_Forest_edgeSetOrders_filter_ne_nil_eq_self_of_nonempty

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    {β : Type*} [AddCommMonoid β]
    {S : Finset (Edge V)} (hS : S.Nonempty)
    (φ : List (Edge V) → β) :
    Finset.sum (edgeSetOrders S) (fun order => φ order) =
      Finset.sum S.attach
        (fun e => Finset.sum (edgeSetOrders (S.erase e.val))
          (fun order => φ (e.val :: order))) := by
  rw [← edgeSetOrders_filter_ne_nil_eq_self_of_nonempty hS]
  exact sum_edgeSetOrders_filter_ne_nil_eq_sum_cons S φ
end BKAR.Forest
