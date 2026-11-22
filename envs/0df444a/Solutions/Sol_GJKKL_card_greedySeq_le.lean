-- Prove2me | solution 1 for GJKKL.card_greedySeq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:26.999706+00:00
-- url     : https://prove2.me/submissions/f950517a-4ad3-4e2b-ac76-afd5bfa944c9

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Greedy_Counting
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_mem_hist
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_IsGreedySeq_nodup
public import Theorems.Thm_GJKKL_IsGreedySeq_toFinset_mem_matchingsOfSize
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_GJKKL_mem_matchingsOfSize
attribute [local simp] GJKKL.History.aliveBefore_cons
attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (hne : ∀ e ∈ H, e.Nonempty) (m : ℕ) :
    ((hist (Finset V) m).filter (IsGreedySeq H)).card ≤
      m.factorial * (matchingsOfSize H m).card := by
  classical
  refine card_le_mul_card_image_of_maps_to (f := List.toFinset) (fun h hh => ?_) _
    (fun M hM => ?_)
  · rw [mem_filter, mem_hist] at hh
    have := hh.2.toFinset_mem_matchingsOfSize hne
    rwa [hh.1] at this
  · have hMm := (mem_matchingsOfSize.mp hM).2.2
    calc ((filter (IsGreedySeq H) (hist (Finset V) m)).filter (fun h => h.toFinset = M)).card
        ≤ M.toList.permutations.toFinset.card := by
          refine card_le_card fun h hh => ?_
          simp only [mem_filter, mem_hist] at hh
          rw [List.mem_toFinset, List.mem_permutations]
          refine List.perm_of_nodup_nodup_toFinset_eq (hh.1.2.nodup hne) M.nodup_toList ?_
          rw [hh.2, toList_toFinset]
      _ ≤ M.toList.permutations.length := List.toFinset_card_le _
      _ = m.factorial := by rw [List.length_permutations, length_toList, hMm]
end GJKKL
