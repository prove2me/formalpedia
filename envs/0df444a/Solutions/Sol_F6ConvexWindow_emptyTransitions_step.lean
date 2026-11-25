-- Prove2me | solution 1 for F6ConvexWindow.emptyTransitions_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:37:00.80053+00:00
-- url     : https://prove2.me/submissions/8f1bf3cf-4007-4d05-a724-fcd5ab27a1b0

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleFamily
import Theorems.Thm_F6ConvexWindow_card_tripleFamily
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_mem_inducedPairs
import Theorems.Thm_F6ConvexWindow_lastTriple_max
import Theorems.Thm_F6ConvexWindow_prefix_overlap_eq_last
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
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) (hn : F.Nonempty)
    (hGn : (F.erase (lastTriple F hn)).Nonempty) :
    emptyTransitions F = emptyTransitions (F.erase (lastTriple F hn)) +
      if Disjoint (lastTriple (F.erase (lastTriple F hn)) hGn) (lastTriple F hn) then 1 else 0 := by
  let T := lastTriple F hn
  let G := F.erase T
  let S := lastTriple G hGn
  have hTF : T ∈ F := lastTriple_mem F hn
  have hSG : S ∈ G := lastTriple_mem G hGn
  have hg : ∀ R ∈ G, IsTriple R := fun R hR => hf R (mem_of_mem_erase hR)
  have hs := hg S hSG
  have ht := hf T hTF
  have hST := ideal_subset_of_card_le hw hci hs.1 ht.1 hs.2 ht.2
    (lastTriple_max F hn S (mem_of_mem_erase hSG))
  have he := prefix_overlap_eq_last hw hci hg hSG (lastTriple_max G hGn) ht hST
  have hd : Disjoint (tripleUnion G) T ↔ Disjoint S T := by
    simp only [disjoint_iff_inter_eq_empty]
    rw [inter_comm (tripleUnion G), he, inter_comm T]
  rw [emptyTransitions, dif_pos hn]
  change emptyTransitions G + (if G.Nonempty ∧ Disjoint (tripleUnion G) T then 1 else 0) =
    emptyTransitions G + (if Disjoint S T then 1 else 0)
  have hGn' : G.Nonempty := hGn
  simp only [hGn', true_and, hd]
end F6ConvexWindow
