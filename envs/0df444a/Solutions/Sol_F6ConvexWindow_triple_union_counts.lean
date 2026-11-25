-- Prove2me | solution 1 for F6ConvexWindow.triple_union_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:14:57.336819+00:00
-- url     : https://prove2.me/submissions/33f109b9-b94e-4c5c-b12e-79961618bc0b

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleFamily
import Theorems.Thm_F6ConvexWindow_card_tripleFamily
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_mem_inducedPairs
import Theorems.Thm_F6ConvexWindow_pairCount_triple
import Theorems.Thm_F6ConvexWindow_lastTriple_max
import Theorems.Thm_F6ConvexWindow_prefix_pairCount_step
import Theorems.Thm_F6ConvexWindow_prefix_intersection_le_one
import Theorems.Thm_F6ConvexWindow_union_card_step
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_ideal_subset_of_card_le
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6ConvexWindow.mem_tripleFamily
attribute [local simp] F6ConvexWindow.card_tripleFamily
attribute [local simp] F6ConvexWindow.mem_tripleUnion
attribute [local simp] F6ConvexWindow.mem_inducedPairs

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) (hn : F.Nonempty) :
    (tripleUnion F).card = 2 * F.card + 1 + emptyTransitions F ∧
    pairCount (tripleUnion F) ≤ 3 * F.card + 3 * emptyTransitions F := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    let T := lastTriple F hn
    have hTF : T ∈ F := lastTriple_mem F hn
    have hTmax : ∀ R ∈ F, (ideal R).card ≤ (ideal T).card := lastTriple_max F hn
    have ht := hf T hTF
    let G := F.erase T
    have hsub : G ⊆ F := erase_subset _ _
    have hg : ∀ R ∈ G, IsTriple R := fun R hR => hf R (hsub hR)
    have hTG : T ∉ G := notMem_erase _ _
    have hF : F = insert T G := (insert_erase hTF).symm
    have hFc : F.card = G.card + 1 := by rw [hF, card_insert_of_notMem hTG]
    have hU : tripleUnion F = tripleUnion G ∪ T := by
      rw [hF]
      simp [tripleUnion, union_comm]
    have hm : emptyTransitions F = emptyTransitions G +
        if G.Nonempty ∧ Disjoint (tripleUnion G) T then 1 else 0 := by
      rw [emptyTransitions, dif_pos hn]
    by_cases hGn : G.Nonempty
    · have ihG := ih G (erase_ssubset hTF) hg hGn
      let S := lastTriple G hGn
      have hSG : S ∈ G := lastTriple_mem G hGn
      have hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card := lastTriple_max G hGn
      have hs := hg S hSG
      have hST := ideal_subset_of_card_le hw hci hs.1 ht.1 hs.2 ht.2 (hTmax S (hsub hSG))
      have hi := prefix_intersection_le_one hw hci hg hSG hSmax ht hST hTG
      have huc := union_card_step ht.2 hi
      have hec := prefix_pairCount_step hw hci hg hSG hSmax ht hST
      simp only [hGn, true_and] at hm
      rw [hU]
      by_cases hd : Disjoint (tripleUnion G) T
      · simp only [if_pos hd] at hm huc hec
        constructor <;> omega
      · simp only [if_neg hd] at hm huc hec
        constructor <;> omega
    · have hGe : G = ∅ := not_nonempty_iff_eq_empty.mp hGn
      have hmG : emptyTransitions G = 0 := by
        rw [hGe, emptyTransitions]
        simp
      have hmF : emptyTransitions F = 0 := by simp [hGn, hmG] at hm; exact hm
      have hFc' : F.card = 1 := by simpa [hGe] using hFc
      have hU' : tripleUnion F = T := by simpa [hGe, tripleUnion] using hU
      rw [hU', hFc', hmF, ht.2, pairCount_triple ht]
      omega
end F6ConvexWindow
