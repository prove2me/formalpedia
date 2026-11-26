-- Prove2me | solution 1 for BKAR.Forest.sum_edgeSetOrders_filter_ne_nil_eq_sum_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:25:45.964094+00:00
-- url     : https://prove2.me/submissions/8825a06f-b3ce-4101-b1d8-233f03967236

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_cons_mem_edgeSetOrders_iff
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrderTails_iff
import Theorems.Thm_BKAR_ForestIndex_ext


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    {β : Type*} [AddCommMonoid β]
    (S : Finset (Edge V)) (φ : List (Edge V) → β) :
    Finset.sum ((edgeSetOrders S).filter (fun order => order ≠ []))
        (fun ord => φ ord) =
      Finset.sum S.attach
        (fun e => Finset.sum (edgeSetOrders (S.erase e.val))
          (fun ord => φ (e.val :: ord))) := by
  have hbij :
      Finset.sum (edgeSetOrderTails S) (fun x => φ (x.1.val :: x.2)) =
        Finset.sum ((edgeSetOrders S).filter (fun order => order ≠ []))
          (fun ord => φ ord) := by
    refine Finset.sum_bij
      (fun x _ => x.1.val :: x.2) ?hi ?hinj ?hsurj ?hφ
    · intro x hx
      rw [Finset.mem_filter]
      constructor
      · rw [cons_mem_edgeSetOrders_iff]
        exact ⟨x.1.property, (mem_edgeSetOrderTails_iff S).mp hx⟩
      · intro hnil
        cases hnil
    · intro x _ y _ hxy
      cases x with
      | mk ex orderX =>
          cases y with
          | mk ey orderY =>
              injection hxy with hhead htail
              have hey : ex = ey := Subtype.ext hhead
              cases hey
              cases htail
              rfl
    · intro ord horder
      rw [Finset.mem_filter] at horder
      rcases horder with ⟨hmem, hne⟩
      cases ord with
      | nil =>
          exact False.elim (hne rfl)
      | cons e ord =>
          have hsplit := (cons_mem_edgeSetOrders_iff S).mp hmem
          refine ⟨⟨⟨e, hsplit.1⟩, ord⟩, ?_, rfl⟩
          rw [mem_edgeSetOrderTails_iff]
          exact hsplit.2
    · intro x _
      rfl
  exact hbij.symm.trans (Finset.sum_sigma S.attach
    (fun e : {e // e ∈ S} => edgeSetOrders (S.erase e.val))
    (fun x : Σ _ : {y : Edge V // y ∈ S}, List (Edge V) =>
      φ (x.1.val :: x.2)))
end BKAR.Forest
