-- Prove2me | solution 1 for BKAR.Forest.mem_edgeSetOrders_iff_toFinset_eq_and_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:44.863291+00:00
-- url     : https://prove2.me/submissions/904676a1-c1d6-419d-9aa5-51f7b14e8f1d

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_iff
import Theorems.Thm_BKAR_ForestIndex_ext


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    (S : Finset (Edge V)) {order : List (Edge V)} :
    order ∈ edgeSetOrders S ↔ order.toFinset = S ∧ order.Nodup := by
  constructor
  · intro h
    have hperm : order.Perm S.toList :=
      (mem_edgeSetOrders_iff S).mp h
    constructor
    · ext e
      rw [List.mem_toFinset, ← Finset.mem_toList]
      exact hperm.mem_iff
    · exact hperm.nodup_iff.mpr (Finset.nodup_toList S)
  · intro h
    rw [mem_edgeSetOrders_iff]
    have htoList : order.toFinset.toList.Perm order :=
      List.toFinset_toList h.2
    have hforest : order.toFinset.toList.Perm S.toList :=
      (Finset.perm_toList).mpr h.1
    exact htoList.symm.trans hforest
end BKAR.Forest
