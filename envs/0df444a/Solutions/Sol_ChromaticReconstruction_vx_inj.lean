-- Prove2me | solution 1 for ChromaticReconstruction.vx_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:42:54.796194+00:00
-- url     : https://prove2.me/submissions/f596ae34-2407-4b41-90ac-d0bd3a120397

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
import Theorems.Thm_ChromaticReconstruction_vx_val
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.vx_val

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n x y : ℕ} (hx : x ≤ n) (hy : y ≤ n) : vx n x = vx n y ↔ x = y := by
  rw [Fin.ext_iff]; simp; omega
end ChromaticReconstruction
