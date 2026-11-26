-- Prove2me | solution 1 for BKAR.Forest.exists_forest_edges_eq_insert_of_mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:03.907828+00:00
-- url     : https://prove2.me/submissions/d39a772e-dc0a-4771-9052-8516a4a0d34e

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_isAcyclicEdgeSet_insert_of_mem_activeEdges


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e₀ : Edge V} (he₀ : e₀ ∈ F.activeEdges) :
    ∃ F' : Forest V, F'.edges = insert e₀ F.edges := by
  rcases F.isAcyclicEdgeSet_insert_of_mem_activeEdges he₀ with ⟨data⟩
  exact ⟨data.toForest, rfl⟩
end BKAR.Forest
