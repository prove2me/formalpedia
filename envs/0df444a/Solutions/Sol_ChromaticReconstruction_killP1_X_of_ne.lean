-- Prove2me | solution 1 for ChromaticReconstruction.killP1_X_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:36:12.630985+00:00
-- url     : https://prove2.me/submissions/e6a337cc-611a-4e73-b44f-62af03ac1c38

import Definitions.Def_RequestProject_Components
import Definitions.Def_RequestProject_PhiFormula
import Theorems.Thm_ChromaticReconstruction_killP1_X
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {r : ℕ} (h : r ≠ 1) : killP1 (X r) = X r := by simp [killP1_X, h]
end ChromaticReconstruction
