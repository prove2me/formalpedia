-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:48.414791+00:00
-- url     : https://prove2.me/submissions/6d0e5842-3f94-45e8-85cd-d1c3702e6e6a

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_acyclic_insert_iff_edge
import Theorems.Thm_BKAR_Forest_mem_activeEdges_of_not_inSameComponent


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e₀) :
    e₀ ∈ F.activeEdges := by
  apply F.mem_activeEdges_of_not_inSameComponent
  have hacyclic : IsAcyclicEdgeSet (insert e₀ F.edges) := by
    rw [← h.edges_eq]
    exact F'.isAcyclicEdgeSet
  exact (F.acyclic_insert_iff_edge h.new_not_mem).mp hacyclic
end BKAR.Forest.EdgeExtension
