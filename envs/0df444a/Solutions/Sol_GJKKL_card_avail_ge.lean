-- Prove2me | solution 1 for GJKKL.card_avail_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:26:47.250945+00:00
-- url     : https://prove2.me/submissions/92b0d6d4-7999-4d65-8d22-f1f6dfbf34df

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_avail_cons
public import Theorems.Thm_GJKKL_avail_subset
public import Theorems.Thm_GJKKL_card_filter_not_disjoint_le
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {k D : ℕ} (hdeg : ∀ v, degree H v ≤ D) :
    ∀ h : List (Finset V), (∀ f ∈ h, f.card ≤ k) →
      H.card ≤ (avail H h).card + h.length * (k * D)
  | [], _ => by simp
  | a :: h, hk => by
    have ih := solution H hdeg h (fun f hf => hk f (List.mem_cons_of_mem a hf))
    have hsplit := card_filter_add_card_filter_not (s := avail H h)
      (fun e => Disjoint e a)
    have hbad : ((avail H h).filter (fun e => ¬ Disjoint e a)).card ≤ k * D := by
      calc ((avail H h).filter (fun e => ¬ Disjoint e a)).card
          ≤ (H.filter (fun e => ¬ Disjoint e a)).card :=
            card_le_card (filter_subset_filter _ (avail_subset H h))
        _ ≤ ∑ v ∈ a, degree H v := card_filter_not_disjoint_le H a
        _ ≤ ∑ _v ∈ a, D := sum_le_sum fun v _ => hdeg v
        _ = a.card * D := by rw [sum_const, smul_eq_mul]
        _ ≤ k * D := Nat.mul_le_mul_right D (hk a List.mem_cons_self)
    rw [avail_cons, List.length_cons]
    nlinarith
end GJKKL
