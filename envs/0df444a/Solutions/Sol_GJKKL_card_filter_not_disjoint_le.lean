-- Prove2me | solution 1 for GJKKL.card_filter_not_disjoint_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:06.380659+00:00
-- url     : https://prove2.me/submissions/bb840459-7bb4-4298-b637-d06ed6760a02

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
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
theorem _root_.solution (H : Finset (Finset V)) (f : Finset V) :
    (H.filter (fun e => ¬ Disjoint e f)).card ≤ ∑ v ∈ f, degree H v := by
  calc (H.filter (fun e => ¬ Disjoint e f)).card
      = (f.biUnion (fun v => H.filter (fun e => v ∈ e))).card := by
        congr 1
        ext e
        simp only [mem_filter, mem_biUnion, Finset.not_disjoint_iff]
        constructor
        · rintro ⟨he, v, hve, hvf⟩; exact ⟨v, hvf, he, hve⟩
        · rintro ⟨v, hvf, he, hve⟩; exact ⟨he, v, hve, hvf⟩
    _ ≤ ∑ v ∈ f, (H.filter (fun e => v ∈ e)).card := card_biUnion_le
    _ = ∑ v ∈ f, degree H v := rfl
end GJKKL
