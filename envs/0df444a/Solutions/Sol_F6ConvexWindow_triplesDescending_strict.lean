-- Prove2me | solution 1 for F6ConvexWindow.triplesDescending_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:54:50.832533+00:00
-- url     : https://prove2.me/submissions/a2354629-dd7d-44ff-966e-ec8a68e7253d

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleFamily
import Theorems.Thm_F6ConvexWindow_card_tripleFamily
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_mem_inducedPairs
import Theorems.Thm_F6ConvexWindow_lastTriple_max
import Theorems.Thm_F6ConvexWindow_triplesDescending_toFinset
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_ideal_injective
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
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) :
    (triplesDescending F).Pairwise (fun T S => ideal S ⊂ ideal T) := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    by_cases hn : F.Nonempty
    · rw [triplesDescending, dif_pos hn, List.pairwise_cons]
      have hT := hf _ (lastTriple_mem F hn)
      constructor
      · intro S hS
        have hm : S ∈ F.erase (lastTriple F hn) := by
          rw [← triplesDescending_toFinset (F.erase (lastTriple F hn))]
          exact List.mem_toFinset.mpr hS
        have hs := hf S (mem_of_mem_erase hm)
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · exact ideal_subset_of_card_le hw hci hs.1 hT.1 hs.2 hT.2
            (lastTriple_max F hn S (mem_of_mem_erase hm))
        · intro he
          exact (mem_erase.mp hm).1 (ideal_injective hs.1 hT.1 he)
      · exact ih _ (erase_ssubset (lastTriple_mem F hn))
          (fun S hS => hf S (mem_of_mem_erase hS))
    · rw [triplesDescending, dif_neg hn]
      simp
end F6ConvexWindow
