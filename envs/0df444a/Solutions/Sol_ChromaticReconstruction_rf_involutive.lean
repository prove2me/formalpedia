-- Prove2me | solution 1 for ChromaticReconstruction.rf_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:03:58.386924+00:00
-- url     : https://prove2.me/submissions/7428a74b-7f28-4c2e-b72a-5025d1303894

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_rfv_le
import Theorems.Thm_ChromaticReconstruction_rfv_rfv
import Theorems.Thm_ChromaticReconstruction_rf_vx
import Theorems.Thm_ChromaticReconstruction_vx_eq_self


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution {s : ℕ} (hs : c + s ≤ n) (hs' : s ≤ c + 1) :
    Function.Involutive (rf n c s) := by
  intro x
  rw [← vx_eq_self x, rf_vx (by omega), rf_vx (rfv_le hs (by omega)), rfv_rfv hs']
end ChromaticReconstruction
