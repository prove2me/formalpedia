-- Prove2me | solution 1 for GJKKL.card_hitters_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:20.160328+00:00
-- url     : https://prove2.me/submissions/cc7ec8be-bbaa-453d-a7f6-78b57b38d8eb

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
public import Theorems.Thm_GJKKL_sum_card_le_card_biUnion_add
public import Theorems.Thm_GJKKL_mem_sdiff_Dv
public import Theorems.Thm_GJKKL_hitters_eq
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_card_avail_both_le_codegree
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
theorem _root_.solution (H : Finset (Finset V)) (h : List (Finset V)) (v : V) (f : Finset V)
    {c : ℕ} (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) :
    ∑ u ∈ f.erase v, dv H h u ≤
      (hitters H h v f).card + (f.erase v).card * c + (f.erase v).card * ((f.erase v).card - 1) * c := by
  set S : V → Finset (Finset V) := fun u => (avail H h \ Dv H h v).filter (fun a => u ∈ a)
  have hbon := sum_card_le_card_biUnion_add (f.erase v) S
  rw [← hitters_eq] at hbon
  -- each `d_u` is `|S u|` plus the edges through both `u` and `v`
  have hdu : ∀ u ∈ f.erase v, dv H h u ≤ (S u).card + c := by
    intro u hu
    have huv : u ≠ v := (mem_erase.mp hu).1
    have hsplit : Dv H h u ⊆ S u ∪ (avail H h).filter (fun e => u ∈ e ∧ v ∈ e) := by
      intro a ha
      rw [mem_Dv] at ha
      by_cases hva : v ∈ a
      · exact mem_union_right _ (mem_filter.mpr ⟨ha.1, ha.2, hva⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_sdiff_Dv.mpr ⟨ha.1, hva⟩, ha.2⟩)
    calc dv H h u ≤ (S u ∪ (avail H h).filter (fun e => u ∈ e ∧ v ∈ e)).card :=
          card_le_card hsplit
      _ ≤ (S u).card + ((avail H h).filter (fun e => u ∈ e ∧ v ∈ e)).card := card_union_le _ _
      _ ≤ (S u).card + c :=
          Nat.add_le_add_left ((card_avail_both_le_codegree H h u v).trans (hc u v huv)) _
  have hpair : ∀ u ∈ f.erase v, ∀ w ∈ (f.erase v).erase u, (S u ∩ S w).card ≤ c := by
    intro u _ w hw
    have hwu : w ≠ u := (mem_erase.mp hw).1
    refine le_trans (card_le_card fun a ha => ?_) ((card_avail_both_le_codegree H h u w).trans
      (hc u w hwu.symm))
    simp only [S, mem_inter, mem_filter, mem_sdiff] at ha
    exact mem_filter.mpr ⟨ha.1.1.1, ha.1.2, ha.2.2⟩
  have h1 : ∑ u ∈ f.erase v, dv H h u ≤ ∑ u ∈ f.erase v, (S u).card + (f.erase v).card * c := by
    calc ∑ u ∈ f.erase v, dv H h u ≤ ∑ u ∈ f.erase v, ((S u).card + c) := sum_le_sum hdu
      _ = _ := by rw [sum_add_distrib, sum_const, smul_eq_mul]
  have h2 : ∑ u ∈ f.erase v, ∑ w ∈ (f.erase v).erase u, (S u ∩ S w).card ≤
      (f.erase v).card * ((f.erase v).card - 1) * c := by
    calc ∑ u ∈ f.erase v, ∑ w ∈ (f.erase v).erase u, (S u ∩ S w).card
        ≤ ∑ u ∈ f.erase v, ∑ _w ∈ (f.erase v).erase u, c :=
          sum_le_sum fun u hu => sum_le_sum fun w hw => hpair u hu w hw
      _ = ∑ u ∈ f.erase v, ((f.erase v).card - 1) * c := by
          refine sum_congr rfl fun u hu => ?_
          rw [sum_const, card_erase_of_mem hu, smul_eq_mul]
      _ = _ := by rw [sum_const, smul_eq_mul, mul_assoc]
  omega
end GJKKL
