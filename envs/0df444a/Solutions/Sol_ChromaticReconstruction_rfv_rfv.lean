-- Prove2me | solution 1 for ChromaticReconstruction.rfv_rfv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:30:22.740716+00:00
-- url     : https://prove2.me/submissions/12227e59-4333-4eb3-ad84-90ed04f7d146

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution {s x : ℕ} (hs : s ≤ c + 1) : rfv c s (rfv c s x) = x := by
  unfold rfv; split_ifs <;> omega
end ChromaticReconstruction
