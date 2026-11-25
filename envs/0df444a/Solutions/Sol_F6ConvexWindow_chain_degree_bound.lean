-- Prove2me | solution 1 for F6ConvexWindow.chain_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:48:11.242801+00:00
-- url     : https://prove2.me/submissions/dc9b9ff7-38dc-4d80-9d43-ecc83022dffa

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_chain_degree_union_bound
import Theorems.Thm_F6ConvexWindow_chain_inc_union_disjoint

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hci : CI2 (V := V)) {C : Finset V}
    (hc : Chain C) (hn : C.Nonempty) :
    (∑ x ∈ C, (Inc x).card) + 2 ≤ Fintype.card V + C.card := by
  have h := chain_degree_union_bound hci C hc hn
  have hdis := chain_inc_union_disjoint hc
  have hcard := card_le_univ (C ∪ C.biUnion Inc)
  rw [card_union_of_disjoint hdis] at hcard
  omega
end F6ConvexWindow
