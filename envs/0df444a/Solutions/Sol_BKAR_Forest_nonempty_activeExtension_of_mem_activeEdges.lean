-- Prove2me | solution 1 for BKAR.Forest.nonempty_activeExtension_of_mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:20:25.991799+00:00
-- url     : https://prove2.me/submissions/5ea1bb1f-369b-428a-968f-1acf06c60dd3

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_nonempty_activeExtension_of_exists_forest_edges_eq_insert
import Theorems.Thm_BKAR_Forest_exists_forest_edges_eq_insert_of_mem_activeEdges

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {e₀ : Edge V} (he₀ : e₀ ∈ F.activeEdges) :
    Nonempty (ActiveExtension F e₀) :=
  nonempty_activeExtension_of_exists_forest_edges_eq_insert he₀
    (F.exists_forest_edges_eq_insert_of_mem_activeEdges he₀)
end BKAR.Forest
