-- Prove2me | solution 1 for ChromaticReconstruction.rfv_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T14:35:50.059046+00:00
-- url     : https://prove2.me/submissions/4504fa31-ab1e-4750-9219-703e7dc4f029

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
theorem _root_.solution {s x : ℕ} (hs : c + s ≤ n) (hx : x ≤ n) : rfv c s x ≤ n := by
  unfold rfv; split_ifs <;> omega
end ChromaticReconstruction
