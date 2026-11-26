-- Prove2me | solution 1 for BKAR.Forest.nonempty_activeExtension_of_exists_forest_edges_eq_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:03.469449+00:00
-- url     : https://prove2.me/submissions/844805a1-b182-4d6d-a6b2-7f34471a5614

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    {F : Forest V} {e₀ : Edge V}
    (he₀ : e₀ ∈ F.activeEdges)
    (hforest : ∃ F' : Forest V, F'.edges = insert e₀ F.edges) :
    Nonempty (ActiveExtension F e₀) := by
  rcases hforest with ⟨F', hedges⟩
  exact ⟨activeExtensionOfEdgesEqInsert he₀ hedges⟩
end BKAR.Forest
