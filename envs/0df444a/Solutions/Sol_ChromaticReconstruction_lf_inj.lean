-- Prove2me | solution 1 for ChromaticReconstruction.lf_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:11:31.794865+00:00
-- url     : https://prove2.me/submissions/b5f4e21a-3998-4bbf-9534-5618273bb667

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
theorem _root_.solution {n p q : ℕ} (hp : p < n) (hq : q < n) : lf n p = lf n q ↔ p = q := by
  simp only [lf, Sym2.eq_iff, Fin.ext_iff, vx_val, min_self]
  constructor
  · intro h; omega
  · intro h; subst h; simp
end ChromaticReconstruction
