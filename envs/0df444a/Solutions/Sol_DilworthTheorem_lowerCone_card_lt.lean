-- Prove2me | solution 1 for DilworthTheorem.lowerCone_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:36:13.461141+00:00
-- url     : https://prove2.me/submissions/6dc69786-dbb6-4424-8899-12618c632376

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
import Theorems.Thm_DilworthTheorem_lowerCone_subset
import Theorems.Thm_DilworthTheorem_cmax_not_mem_lowerCone

set_option autoImplicit true
open DilworthTheorem
open Finset
open Classical
variable {α : Type*} [PartialOrder α]
namespace DilworthTheorem
theorem _root_.solution {S A C : Finset α} {cmax : α}
    (hAS : A ⊆ S) (hCS : C ⊆ S) (hcmax_in : cmax ∈ C)
    (hcmax_max : ∀ x ∈ S, cmax ≤ x → x = cmax)
    (hAC_disj : Disjoint A C) :
    (lowerCone S A).card < S.card := by
  refine card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨lowerCone_subset S A, fun h => ?_⟩)
  have hc : cmax ∈ lowerCone S A := by rw [h]; exact hCS hcmax_in
  exact cmax_not_mem_lowerCone hAS hcmax_in hcmax_max hAC_disj hc
end DilworthTheorem
