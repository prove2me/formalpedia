-- Prove2me | solution 1 for ChromaticReconstruction.edgeFinset_PL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:09:09.907451+00:00
-- url     : https://prove2.me/submissions/41aeba7c-692d-45c4-8141-2acbd3a1b47c

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
import Theorems.Thm_ChromaticReconstruction_vx_val
import Theorems.Thm_ChromaticReconstruction_mem_edgeSet_PL
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.vx_val

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n c : ℕ} (hc : c < n) :
    (PL n c).edgeFinset = insert (lf n c) ((range (n - 1)).image (pe n)) := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, mem_edgeSet_PL hc, mem_insert, mem_image]
  constructor
  · rintro (⟨i, hi, rfl⟩ | h)
    · exact Or.inr ⟨i, by rw [mem_range]; omega, rfl⟩
    · exact Or.inl h
  · rintro (h | ⟨i, hi, rfl⟩)
    · exact Or.inr h
    · rw [mem_range] at hi
      exact Or.inl ⟨i, by omega, rfl⟩
end ChromaticReconstruction
