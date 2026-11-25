-- Prove2me | solution 1 for ChromaticReconstruction.card_compSets_le_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:38:34.775994+00:00
-- url     : https://prove2.me/submissions/0aab6a19-81c2-4afa-a5b6-304a449a0f4b

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
import Theorems.Thm_ChromaticReconstruction_card_compSets_le_insert
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (A D : Finset (Sym2 V)) :
    (compSets (A : Set (Sym2 V))).card ≤ (compSets ((A ∪ D : Finset _) : Set (Sym2 V))).card +
      D.card := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert d D hd ih =>
    rw [card_insert_of_notMem hd, union_insert, coe_insert]
    have := card_compSets_le_insert ((A ∪ D : Finset _) : Set (Sym2 V)) d
    omega
end ChromaticReconstruction
