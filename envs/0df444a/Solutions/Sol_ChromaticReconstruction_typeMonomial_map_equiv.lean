-- Prove2me | solution 1 for ChromaticReconstruction.typeMonomial_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:07:41.851394+00:00
-- url     : https://prove2.me/submissions/bcd4d20a-8106-4d6e-849d-c278738ce1d6

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
import Theorems.Thm_ChromaticReconstruction_compSets_map_equiv

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution (e : V ≃ W) (A : Set (Sym2 V)) :
    typeMonomial (Sym2.map e '' A) = typeMonomial A := by
  unfold typeMonomial
  rw [compSets_map_equiv, prod_image]
  · simp
  · intro C _ D _ h
    exact Finset.map_injective _ h
end ChromaticReconstruction
