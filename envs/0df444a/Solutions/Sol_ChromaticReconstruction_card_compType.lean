-- Prove2me | solution 1 for ChromaticReconstruction.card_compType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:36:13.282883+00:00
-- url     : https://prove2.me/submissions/ebd3adab-374f-47f5-bfd6-04876237d82f

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
theorem _root_.solution (A : Set (Sym2 V)) : Multiset.card (compType A) = (compSets A).card := by
  simp [compType]
end ChromaticReconstruction
