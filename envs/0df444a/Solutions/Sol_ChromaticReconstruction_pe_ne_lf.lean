-- Prove2me | solution 1 for ChromaticReconstruction.pe_ne_lf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:36:13.772232+00:00
-- url     : https://prove2.me/submissions/e3da7bbd-94c9-4506-98b8-ac4dfda36f88

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
theorem _root_.solution {n i p : ℕ} (hi : i + 1 < n) (hp : p ≤ n) : pe n i ≠ lf n p := by
  simp only [pe, lf, ne_eq, Sym2.eq_iff, Fin.ext_iff, vx_val]
  omega
end ChromaticReconstruction
