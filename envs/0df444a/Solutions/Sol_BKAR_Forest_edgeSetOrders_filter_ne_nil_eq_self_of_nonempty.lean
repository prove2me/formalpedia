-- Prove2me | solution 1 for BKAR.Forest.edgeSetOrders_filter_ne_nil_eq_self_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:49:54.826328+00:00
-- url     : https://prove2.me/submissions/63a26099-f6c9-443b-bbc6-a964465574f3

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeSetOrders
import Theorems.Thm_BKAR_ForestIndex_ext


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    {S : Finset (Edge V)} (hS : S.Nonempty) :
    (edgeSetOrders S).filter (fun order => order ≠ []) = edgeSetOrders S := by
  ext order
  rw [Finset.mem_filter]
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, ?_⟩
    intro hnil
    subst order
    rcases hS with ⟨e, he⟩
    have hset := toFinset_eq_of_mem_edgeSetOrders h
    rw [List.toFinset_nil] at hset
    rw [← hset] at he
    exact Finset.notMem_empty e he
end BKAR.Forest
