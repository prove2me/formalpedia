-- Prove2me | solution 1 for ChromaticReconstruction.card_compSets_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:25:50.419399+00:00
-- url     : https://prove2.me/submissions/5b4aa68c-ab32-49e2-8633-a10f44c9f33f

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
import Theorems.Thm_ChromaticReconstruction_card_compType
import Theorems.Thm_ChromaticReconstruction_compType_empty


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution : (compSets (∅ : Set (Sym2 V))).card = Fintype.card V := by
  rw [← card_compType, compType_empty, Multiset.card_replicate]
end ChromaticReconstruction
