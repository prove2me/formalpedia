-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.activeEdges_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:43.037787+00:00
-- url     : https://prove2.me/submissions/ed483f49-8f49-402e-866d-6e8ca5c49775

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_EdgeExtension_mem_activeEdges
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_subset_erase

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e₀) :
    F'.activeEdges.card < F.activeEdges.card := by
  have hsubset : F'.activeEdges ⊆ F.activeEdges.erase e₀ :=
    h.activeEdges_subset_erase
  exact (Finset.card_le_card hsubset).trans_lt
    (Finset.card_erase_lt_of_mem h.mem_activeEdges)
end BKAR.Forest.EdgeExtension
