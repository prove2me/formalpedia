-- Prove2me | solution 1 for ChromaticReconstruction.card_compSets_add_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:37:41.340693+00:00
-- url     : https://prove2.me/submissions/4ff83618-1b47-4cd9-9134-5098f552dd1b

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
import Theorems.Thm_ChromaticReconstruction_card_compSets_le_insert
import Theorems.Thm_ChromaticReconstruction_card_compSets_empty
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (A : Finset (Sym2 V)) :
    Fintype.card V ≤ (compSets (A : Set (Sym2 V))).card + A.card := by
  induction A using Finset.induction_on with
  | empty => simp [card_compSets_empty]
  | insert e A he ih =>
    rw [coe_insert, card_insert_of_notMem he]
    have := card_compSets_le_insert (A : Set (Sym2 V)) e
    omega
end ChromaticReconstruction
