-- Prove2me | solution 1 for F6ConvexWindow.triple_union_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:52:03.442416+00:00
-- url     : https://prove2.me/submissions/3ba65b77-6c6e-46b8-9db6-d78568ce9ed2

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_no_reentry
import Theorems.Thm_F6ConvexWindow_triple_intersection_le_one
import Theorems.Thm_F6ConvexWindow_ideal_subset_of_card_le
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
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, Antichain T ∧ T.card = 3)
    (hn : F.Nonempty) : 2 * F.card + 1 ≤ (F.biUnion id).card := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    obtain ⟨T, hTF, hTmax⟩ := exists_max_image F (fun T => (ideal T).card) hn
    have ht := hf T hTF
    let G := F.erase T
    have hsub : G ⊆ F := erase_subset _ _
    have hg : ∀ S ∈ G, Antichain S ∧ S.card = 3 := fun S hS => hf S (hsub hS)
    have hF : F = insert T G := (insert_erase hTF).symm
    have hTc : F.card = G.card + 1 := by
      rw [hF, card_insert_of_notMem (notMem_erase _ _)]
    have hU : F.biUnion id = T ∪ G.biUnion id := by rw [hF, biUnion_insert]; rfl
    by_cases hGn : G.Nonempty
    · have ihG := ih G (erase_ssubset hTF) hg hGn
      obtain ⟨S, hSG, hSmax⟩ := exists_max_image G (fun S => (ideal S).card) hGn
      have hs := hg S hSG
      have hST : ideal S ⊆ ideal T :=
        ideal_subset_of_card_le hw hci hs.1 ht.1 hs.2 ht.2 (hTmax S (hsub hSG))
      have hi : (T ∩ G.biUnion id) ⊆ T ∩ S := by
        intro x hx
        obtain ⟨hxT, hxU⟩ := mem_inter.mp hx
        obtain ⟨R, hRG, hxR⟩ := mem_biUnion.mp hxU
        have hr := hg R hRG
        have hRS : ideal R ⊆ ideal S :=
          ideal_subset_of_card_le hw hci hr.1 hs.1 hr.2 hs.2 (hSmax R hRG)
        exact mem_inter.mpr ⟨hxT, no_reentry ht.1 hRS hST hxR hxT⟩
      have hne : T ≠ S := (mem_erase.mp hSG).1.symm
      have hI := (card_le_card hi).trans
        (triple_intersection_le_one hw hci ht.1 hs.1 ht.2 hs.2 hne)
      have hcount := card_union_add_card_inter T (G.biUnion id)
      rw [hU]
      omega
    · have hGe : G = ∅ := not_nonempty_iff_eq_empty.mp hGn
      rw [hU, hGe]
      simp only [biUnion_empty, union_empty]
      simp only [hGe, card_empty] at hTc
      omega
end F6ConvexWindow
