-- Prove2me | solution 1 for ChromaticReconstruction.pe_mem_edgeSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:09:08.671341+00:00
-- url     : https://prove2.me/submissions/d01b6dc8-09a5-4a5f-a9b1-01401413302d

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
import Theorems.Thm_ChromaticReconstruction_mem_edgeSet_PL

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n c i : ℕ} (hc : c < n) (hi : i + 1 < n) : pe n i ∈ (PL n c).edgeSet :=
  (mem_edgeSet_PL hc _).2 (Or.inl ⟨i, hi, rfl⟩)
end ChromaticReconstruction
