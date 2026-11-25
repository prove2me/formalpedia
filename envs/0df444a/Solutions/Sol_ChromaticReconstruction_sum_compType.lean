-- Prove2me | solution 1 for ChromaticReconstruction.sum_compType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:24.533896+00:00
-- url     : https://prove2.me/submissions/0269808d-ed5f-4afd-83ca-c47fb29e7cf0

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_sum_card_compSets

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (A : Set (Sym2 V)) : (compType A).sum = Fintype.card V := by
  rw [compType, ← sum_card_compSets A]
  rfl
end ChromaticReconstruction
