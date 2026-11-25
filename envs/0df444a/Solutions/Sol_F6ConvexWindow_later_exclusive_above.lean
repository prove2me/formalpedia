-- Prove2me | solution 1 for F6ConvexWindow.later_exclusive_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:11:38.042677+00:00
-- url     : https://prove2.me/submissions/0ddee2f4-20c0-4458-a98f-344b8dbd2aca

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_below_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_subset_ideal
import Theorems.Thm_F6ConvexWindow_triple_split
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
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T)
    (hST : ideal S ⊆ ideal T) {y : V} (hyT : y ∈ T) (hyS : y ∉ S) : Above S y := by
  have hyI : y ∉ ideal S := by
    intro h
    obtain ⟨s, hsS, hys⟩ := mem_ideal.mp h
    obtain ⟨z, hzT, hsz⟩ := mem_ideal.mp (hST (subset_ideal S hsS))
    have hyz := ht.1 y hyT z hzT (hys.trans hsz)
    have hsy : s = y := le_antisymm (hyz.symm ▸ hsz) hys
    exact hyS (hsy ▸ hsS)
  exact (triple_split hw hci hs.1 hs.2 hyS).resolve_left
    (fun h => hyI (below_mem_ideal h))
end F6ConvexWindow
