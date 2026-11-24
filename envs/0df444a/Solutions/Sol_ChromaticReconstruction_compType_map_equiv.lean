-- Prove2me | solution 1 for ChromaticReconstruction.compType_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T12:02:34.419623+00:00
-- url     : https://prove2.me/submissions/9dd761aa-df2b-4a4f-a77a-707d52483dfb

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
    compType (Sym2.map e '' A) = compType A := by
  unfold compType
  rw [compSets_map_equiv, image_val_of_injOn]
  · simp [Multiset.map_map]
  · intro C _ D _ h
    exact Finset.map_injective _ h
end ChromaticReconstruction
