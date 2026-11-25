-- Prove2me | solution 1 for ChromaticReconstruction.pe_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:57:46.069094+00:00
-- url     : https://prove2.me/submissions/243223a9-e841-4d1e-94de-6d8f860e29d6

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
theorem _root_.solution {n i j : ℕ} (hi : i + 1 ≤ n) (hj : j + 1 ≤ n) : pe n i = pe n j ↔ i = j := by
  simp only [pe, Sym2.eq_iff, Fin.ext_iff, vx_val]
  omega
end ChromaticReconstruction
