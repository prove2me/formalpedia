-- Prove2me | solution 1 for DilworthTheorem.upperCone_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:36:15.547563+00:00
-- url     : https://prove2.me/submissions/258fefab-7ee5-4ca1-a97b-01d79e06e078

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Antichain
import Mathlib.Tactic
import Definitions.Def_StableMarriageF6_DilworthTheorem
import Theorems.Thm_DilworthTheorem_upperCone_subset
import Theorems.Thm_DilworthTheorem_cmin_not_mem_upperCone

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution {S A C : Finset α} {cmin : α}
    (hAS : A ⊆ S) (hCS : C ⊆ S) (hcmin_in : cmin ∈ C)
    (hcmin_min : ∀ x ∈ S, x ≤ cmin → x = cmin)
    (hAC_disj : Disjoint A C) :
    (upperCone S A).card < S.card := by
  refine card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨upperCone_subset S A, fun h => ?_⟩)
  have hc : cmin ∈ upperCone S A := by rw [h]; exact hCS hcmin_in
  exact cmin_not_mem_upperCone hAS hcmin_in hcmin_min hAC_disj hc
end DilworthTheorem
