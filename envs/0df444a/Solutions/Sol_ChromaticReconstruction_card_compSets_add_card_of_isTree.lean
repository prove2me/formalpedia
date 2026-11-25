-- Prove2me | solution 1 for ChromaticReconstruction.card_compSets_add_card_of_isTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:57.64515+00:00
-- url     : https://prove2.me/submissions/ee8b413a-d114-4592-b426-d213e1c44129

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
import Theorems.Thm_ChromaticReconstruction_card_compSets_edgeSet_of_connected
import Theorems.Thm_ChromaticReconstruction_card_compSets_add_card_ge
import Theorems.Thm_ChromaticReconstruction_card_compSets_le_union

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {S : SimpleGraph V} (hS : S.IsTree)
    {F : Finset (Sym2 V)} (hF : F ⊆ S.edgeFinset) :
    (compSets (F : Set (Sym2 V))).card + F.card = Fintype.card V := by
  have hge := card_compSets_add_card_ge F
  have hle := card_compSets_le_union F (S.edgeFinset \ F)
  rw [union_sdiff_of_subset hF, SimpleGraph.coe_edgeFinset, card_compSets_edgeSet_of_connected hS.1,
    card_sdiff_of_subset hF] at hle
  have := hS.card_edgeFinset
  have : F.card ≤ S.edgeFinset.card := card_le_card hF
  omega
end ChromaticReconstruction
