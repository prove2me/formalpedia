-- Prove2me | solution 1 for F6ConvexWindow.chain_degree_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:41:55.916695+00:00
-- url     : https://prove2.me/submissions/4f566dcf-de79-4b4e-aecb-e2fd7fc8227f

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_adjacent_common_bound
import Theorems.Thm_F6ConvexWindow_chain_greatest
import Theorems.Thm_F6ConvexWindow_chain_adjacent_overlap
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_ideal
attribute [local simp] F6ConvexWindow.mem_antichains

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hci : CI2 (V := V)) (C : Finset V)
    (hc : Chain C) (hn : C.Nonempty) :
    (∑ x ∈ C, (Inc x).card) + 2 ≤ (C.biUnion Inc).card + 2 * C.card := by
  classical
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    obtain ⟨y, hyC, hymax⟩ := chain_greatest hc hn
    let D := C.erase y
    have hsub : D ⊆ C := erase_subset _ _
    have hd : Chain D := fun a ha b hb => hc a (hsub ha) b (hsub hb)
    have hC : C = insert y D := (insert_erase hyC).symm
    have hyD : y ∉ D := notMem_erase _ _
    have hcard : C.card = D.card + 1 := by rw [hC, card_insert_of_notMem hyD]
    have hsum : (∑ x ∈ C, (Inc x).card) = (Inc y).card + ∑ x ∈ D, (Inc x).card := by
      rw [hC, sum_insert hyD]
    have hunion : C.biUnion Inc = D.biUnion Inc ∪ Inc y := by
      rw [hC, biUnion_insert, union_comm]
    by_cases hnD : D.Nonempty
    · obtain ⟨x, hxD, hxmax⟩ := chain_greatest hd hnD
      have hxy : x < y := (hymax x (hsub hxD)).lt_of_ne (mem_erase.mp hxD).1
      have hover := chain_adjacent_overlap hxD hxmax hxy.le
      have hbound : ((D.biUnion Inc) ∩ Inc y).card ≤ 2 := by
        rw [hover]
        exact adjacent_common_bound hci hxy
      have hrec := ih D (erase_ssubset hyC) hd hnD
      have hcount := card_union_add_card_inter (D.biUnion Inc) (Inc y)
      rw [hsum, hunion, hcard]
      omega
    · have hDe : D = ∅ := not_nonempty_iff_eq_empty.mp hnD
      rw [hsum, hunion, hcard, hDe]
      simp
end F6ConvexWindow
