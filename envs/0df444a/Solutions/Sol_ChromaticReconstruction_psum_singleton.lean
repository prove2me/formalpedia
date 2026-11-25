-- Prove2me | solution 1 for ChromaticReconstruction.psum_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:36:04.281215+00:00
-- url     : https://prove2.me/submissions/48116ac9-2755-4602-9fb6-63f226c68dfa

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (j a : ℕ) : psum j {a} = (a : ℤ) ^ j := by simp [psum]
end ChromaticReconstruction
