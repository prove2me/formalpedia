-- Prove2me | solution 1 for GJKKL.card_hitters_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:31.820798+00:00
-- url     : https://prove2.me/submissions/eec4bf5b-7c36-46b4-83e5-662e685feb8c

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
public import Theorems.Thm_GJKKL_hitters_eq
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_GJKKL_mem_Dv
attribute [local simp] GJKKL.Dv_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (h : List (Finset V)) (v : V) (f : Finset V) :
    (hitters H h v f).card ≤ ∑ u ∈ f.erase v, dv H h u := by
  rw [hitters_eq]
  refine card_biUnion_le.trans (sum_le_sum fun u _ => card_le_card fun a ha => ?_)
  simp only [mem_filter, mem_sdiff] at ha
  exact mem_Dv.mpr ⟨ha.1.1, ha.2⟩
end GJKKL
