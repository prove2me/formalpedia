-- Prove2me | solution 1 for BKAR.Forest.eq_and_tail_eq_nil_of_cons_toFinset_eq_singleton_of_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:54.806802+00:00
-- url     : https://prove2.me/submissions/a2dc94a4-5c02-44fc-86c2-7b8b37b79b6f

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    {e a : Edge V} {tail : List (Edge V)}
    (hset : (e :: tail).toFinset = ({a} : Finset (Edge V)))
    (hnodup : (e :: tail).Nodup) :
    e = a ∧ tail = [] := by
  have heq : e = a := by
    have he_mem : e ∈ ({a} : Finset (Edge V)) := by
      rw [← hset]
      exact List.mem_toFinset.mpr (by
        rw [List.mem_cons]
        exact Or.inl rfl)
    exact Finset.mem_singleton.mp he_mem
  have htail : tail = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    have hx_single : x = a := by
      have hx_mem : x ∈ ({a} : Finset (Edge V)) := by
        rw [← hset]
        exact List.mem_toFinset.mpr (List.mem_cons_of_mem e hx)
      exact Finset.mem_singleton.mp hx_mem
    have hxe : x = e := by
      rw [hx_single, ← heq]
    exact hnodup.notMem (hxe ▸ hx)
  exact ⟨heq, htail⟩
end BKAR.Forest
