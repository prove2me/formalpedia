-- Prove2me | solution 1 for ChromaticReconstruction.rf_vx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:58:55.780976+00:00
-- url     : https://prove2.me/submissions/bb9ea750-ab54-469b-91ad-befc44436d97

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_vx_val
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.vx_val



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution {s x : ℕ} (hx : x ≤ n) : rf n c s (vx n x) = vx n (rfv c s x) := by
  unfold rf; simp [min_eq_left hx]
end ChromaticReconstruction
