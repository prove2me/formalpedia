-- Prove2me | solution 1 for GJKKL.sum_card_le_card_biUnion_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:28.413531+00:00
-- url     : https://prove2.me/submissions/38f58e32-38e5-4d32-a17f-b8bc90908263

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
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
namespace GJKKL
theorem _root_.solution {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (s : Finset ι) (S : ι → Finset β) :
    ∑ i ∈ s, (S i).card ≤
      (s.biUnion S).card + ∑ i ∈ s, ∑ j ∈ s.erase i, (S i ∩ S j).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, biUnion_insert, sum_insert hi, erase_insert hi]
    have hun := card_union_add_card_inter (S i) (s.biUnion S)
    have hint : (S i ∩ s.biUnion S).card ≤ ∑ j ∈ s, (S i ∩ S j).card := by
      rw [inter_biUnion]; exact card_biUnion_le
    have hmono : ∑ i' ∈ s, ∑ j ∈ s.erase i', (S i' ∩ S j).card ≤
        ∑ i' ∈ s, ∑ j ∈ (insert i s).erase i', (S i' ∩ S j).card :=
      sum_le_sum fun i' _ => sum_le_sum_of_subset (erase_subset_erase _ (subset_insert _ _))
    omega
end GJKKL
