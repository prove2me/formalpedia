-- Prove2me | solution 1 for ChromaticReconstruction.mem_compType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:41:09.311454+00:00
-- url     : https://prove2.me/submissions/1f9cea73-dba9-4307-871a-c2ef12d5b987

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A : Set (Sym2 V)} {r : ℕ} :
    r ∈ compType A ↔ ∃ C ∈ compSets A, C.card = r := by
  simp [compType]
end ChromaticReconstruction
