-- Prove2me | solution 1 for ChromaticReconstruction.lf_mem_edgeSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:58:05.792148+00:00
-- url     : https://prove2.me/submissions/4c3594c1-2a9c-43fd-9160-c3d1077173ac

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
import Theorems.Thm_ChromaticReconstruction_mem_edgeSet_PL

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n c : ℕ} (hc : c < n) : lf n c ∈ (PL n c).edgeSet :=
  (mem_edgeSet_PL hc _).2 (Or.inr rfl)
end ChromaticReconstruction
