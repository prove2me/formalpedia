-- Prove2me | solution 1 for ChromaticReconstruction.sum_card_compSets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:45.016854+00:00
-- url     : https://prove2.me/submissions/517b4930-3dbb-4059-bbd2-7a26486a2414

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_sum_compOf
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (A : Set (Sym2 V)) : ∑ C ∈ compSets A, C.card = Fintype.card V := by
  have := sum_compOf A (fun _ => (1 : ℕ))
  simp only [sum_const, card_univ, smul_eq_mul, mul_one] at this
  rw [← this]
end ChromaticReconstruction
