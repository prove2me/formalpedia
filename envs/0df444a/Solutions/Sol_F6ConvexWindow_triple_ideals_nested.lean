-- Prove2me | solution 1 for F6ConvexWindow.triple_ideals_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:39:32.387827+00:00
-- url     : https://prove2.me/submissions/a560f886-ed38-43e4-bae7-e486bab0b34e

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_subset_ideal
import Theorems.Thm_F6ConvexWindow_ideal_mono
import Theorems.Thm_F6ConvexWindow_triple_comparison
import Theorems.Thm_F6ConvexWindow_triple_split
import Theorems.Thm_F6ConvexWindow_below_lt_above
import Theorems.Thm_F6ConvexWindow_below_mem_ideal
import Theorems.Thm_F6ConvexWindow_above_not_le
attribute [local simp] F6ConvexWindow.mem_ideal

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : Antichain S) (ht : Antichain T)
    (hsc : S.card = 3) (htc : T.card = 3) :
    ideal S ⊆ ideal T ∨ ideal T ⊆ ideal S := by
  classical
  by_cases hu : ∃ u ∈ S, Above T u
  · right
    obtain ⟨u, huS, huT⟩ := hu
    have hnlow : ∀ l ∈ S, ¬ Below T l := by
      intro l hlS hlT
      have hlu := below_lt_above htc hlT huT
      exact hlu.ne (hs l hlS u huS hlu.le)
    apply ideal_mono
    intro t htT
    by_cases htS : t ∈ S
    · exact subset_ideal S htS
    obtain ⟨s, hsS, hts | hst⟩ := triple_comparison hw hs hsc htS
    · exact mem_ideal.mpr ⟨s, hsS, hts⟩
    · by_cases hsT : s ∈ T
      · have hst' := ht s hsT t htT hst
        exact False.elim (htS (hst' ▸ hsS))
      · rcases triple_split hw hci ht htc hsT with hlow | hhigh
        · exact False.elim (hnlow s hsS hlow)
        · exact False.elim (above_not_le ht hhigh htT hst)
  · left
    apply ideal_mono
    intro s hsS
    by_cases hsT : s ∈ T
    · exact subset_ideal T hsT
    rcases triple_split hw hci ht htc hsT with hlow | hhigh
    · exact below_mem_ideal hlow
    · exact False.elim (hu ⟨s, hsS, hhigh⟩)
end F6ConvexWindow
