-- Prove2me | solution 1 for Formalism.G0.WalkSharpP.done_move
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:09.098881+00:00
-- url     : https://prove2.me/submissions/91f52dc3-c9d5-4c14-90c7-a239e8c13f70

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Theorems.Thm_Formalism_G0_WalkSharpP_le_top
import Theorems.Thm_Formalism_G0_WalkSharpP_top_mem
import Theorems.Thm_Formalism_G0_WalkSharpP_top_move

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.WalkSharpP
namespace Formalism.G0.WalkSharpP
theorem _root_.solution {V : ℕ} {B : Finset (Fin V)} {v w u : Fin V} (hv : v ∈ B)
    (hw : (w : ℕ) = top B + 1) :
    ((u : ℕ) < top (insert w (B.erase v)) ∧ u ∉ insert w (B.erase v)) ↔
      (((u : ℕ) < top B ∧ u ∉ B) ∨ u = v) := by

  obtain ⟨t, ht, htB⟩ := top_mem ⟨v, hv⟩
  rw [top_move hw]
  constructor
  · rintro ⟨hlt, hnot⟩
    by_cases huv : u = v
    · exact Or.inr huv
    · left
      have hnB : u ∉ B := fun h => hnot (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨huv, h⟩))
      refine ⟨?_, hnB⟩
      rcases Nat.lt_or_ge (u : ℕ) (top B) with h | h
      · exact h
      · exfalso
        have hut : u = t := Fin.ext (by omega)
        exact hnB (by rw [hut]; exact ht)
  · rintro (⟨hlt, hnB⟩ | rfl)
    · refine ⟨by omega, ?_⟩
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · have := congrArg Fin.val h
        omega
      · exact hnB (Finset.mem_of_mem_erase h)
    · have := le_top hv
      refine ⟨by omega, ?_⟩
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · have := congrArg Fin.val h
        omega
      · exact (Finset.mem_erase.mp h).1 rfl
end Formalism.G0.WalkSharpP
