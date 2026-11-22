-- Prove2me | solution 1 for GJKKL.card_loss_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:32.252073+00:00
-- url     : https://prove2.me/submissions/a0d260d0-bea9-460e-a27a-f99876ca180b

module
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Definitions.Def_GJKKL_Greedy_Drift
public import Theorems.Thm_GJKKL_avail_subset
public import Theorems.Thm_GJKKL_mem_Dv


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (h : List (Finset V)) {v : V} {a : Finset V}
    (hva : v ∉ a) {c : ℕ} (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) :
    ((Dv H h v).filter (fun f => ¬ Disjoint f a)).card ≤ a.card * c := by
  calc ((Dv H h v).filter (fun f => ¬ Disjoint f a)).card
      ≤ (a.biUnion (fun x => H.filter (fun f => v ∈ f ∧ x ∈ f))).card := by
        refine card_le_card fun f hf => ?_
        rw [mem_filter, mem_Dv, Finset.not_disjoint_iff] at hf
        obtain ⟨⟨hfA, hvf⟩, x, hxf, hxa⟩ := hf
        exact mem_biUnion.mpr ⟨x, hxa, mem_filter.mpr ⟨avail_subset H h hfA, hvf, hxf⟩⟩
    _ ≤ ∑ x ∈ a, (H.filter (fun f => v ∈ f ∧ x ∈ f)).card := card_biUnion_le
    _ ≤ ∑ _x ∈ a, c := sum_le_sum fun x hx => hc v x (fun hvx => hva (hvx ▸ hx))
    _ = a.card * c := by rw [sum_const, smul_eq_mul]
end GJKKL
