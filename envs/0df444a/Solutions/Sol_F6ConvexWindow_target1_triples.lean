-- Prove2me | solution 1 for F6ConvexWindow.target1_triples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:57:41.395975+00:00
-- url     : https://prove2.me/submissions/97414ebc-9dc2-421f-9bb0-ceb34b4cc817

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_triple_union_lower_bound
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
    (hpos : 0 < Ak (V := V) 3) : 2 * Ak (V := V) 3 + 1 ≤ Fintype.card V := by
  classical
  let F := (antichains (V := V)).filter (fun T => T.card = 3)
  have hf : ∀ T ∈ F, Antichain T ∧ T.card = 3 := by
    intro T hT
    exact ⟨mem_antichains.mp (mem_filter.mp hT).1, (mem_filter.mp hT).2⟩
  have hn : F.Nonempty := card_pos.mp hpos
  exact (triple_union_lower_bound hw hci F hf hn).trans (card_le_univ _)
end F6ConvexWindow
