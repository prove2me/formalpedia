-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.activeEdges_subset_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:40.303163+00:00
-- url     : https://prove2.me/submissions/6f92764a-4f40-4615-be4a-de933cfd80c3

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_EdgeExtension_new_mem
import Theorems.Thm_BKAR_Forest_mem_activeEdges_of_not_inSameComponent
import Theorems.Thm_BKAR_Forest_not_inSameComponent_of_mem_activeEdges


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e₀) :
    F'.activeEdges ⊆ F.activeEdges.erase e₀ := by
  intro e he
  rw [Finset.mem_erase]
  constructor
  · intro heq
    subst e
    exact (F'.not_inSameComponent_of_mem_activeEdges he)
      (F'.edge_inSameComponent h.new_mem)
  · apply F.mem_activeEdges_of_not_inSameComponent
    intro hcomp
    exact (F'.not_inSameComponent_of_mem_activeEdges he)
      (h.old_component hcomp)
end BKAR.Forest.EdgeExtension
