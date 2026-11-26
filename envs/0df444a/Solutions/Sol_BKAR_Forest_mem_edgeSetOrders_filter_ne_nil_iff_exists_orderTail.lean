-- Prove2me | solution 1 for BKAR.Forest.mem_edgeSetOrders_filter_ne_nil_iff_exists_orderTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:27:01.12768+00:00
-- url     : https://prove2.me/submissions/084f49cf-34b7-40ae-96bd-bf243cf9dc15

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_cons_mem_edgeSetOrders_iff
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrderTails_iff

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKAR.Forest
theorem _root_.solution
    (S : Finset (Edge V)) {order : List (Edge V)} :
    order ∈ (edgeSetOrders S).filter (fun order => order ≠ []) ↔
      ∃ x ∈ edgeSetOrderTails S, x.1.val :: x.2 = order := by
  rw [Finset.mem_filter]
  constructor
  · intro h
    rcases h with ⟨hmem, hne⟩
    cases order with
    | nil =>
        exact False.elim (hne rfl)
    | cons e order =>
        have hsplit := (cons_mem_edgeSetOrders_iff S).mp hmem
        refine ⟨⟨⟨e, hsplit.1⟩, order⟩, ?_, rfl⟩
        rw [mem_edgeSetOrderTails_iff]
        exact hsplit.2
  · intro h
    rcases h with ⟨x, hx, horder⟩
    rw [← horder]
    constructor
    · rw [cons_mem_edgeSetOrders_iff]
      exact ⟨x.1.property, (mem_edgeSetOrderTails_iff S).mp hx⟩
    · intro hnil
      cases hnil
end BKAR.Forest
