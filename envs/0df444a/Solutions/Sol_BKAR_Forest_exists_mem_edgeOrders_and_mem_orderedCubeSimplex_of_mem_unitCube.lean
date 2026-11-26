-- Prove2me | solution 1 for BKAR.Forest.exists_mem_edgeOrders_and_mem_orderedCubeSimplex_of_mem_unitCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:47.264266+00:00
-- url     : https://prove2.me/submissions/494c3115-0276-482c-880a-3ab11a13bb6c

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Theorems.Thm_BKAR_Forest_mem_unitCube_iff
import Theorems.Thm_BKAR_Forest_mem_orderedCubeSimplex_iff
import Theorems.Thm_BKAR_Forest_orderedSimplexParams_map_paramValue_of_pairwise_ge
import Theorems.Thm_BKAR_Forest_mem_edgeOrders_iff
import Theorems.Thm_BKAR_Forest_paramValue_mem_Icc


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) {u : F.EdgeParam → ℝ} (hu : u ∈ F.unitCube) :
    ∃ order : List (Edge V),
      order ∈ F.edgeOrders ∧ u ∈ F.orderedCubeSimplex order := by
  classical
  let r : Edge V → Edge V → Prop :=
    fun e e' => F.paramValue u e' ≤ F.paramValue u e
  have : DecidableRel r := Classical.decRel r
  have : IsTrans (Edge V) r := ⟨fun _ _ _ hab hbc => hbc.trans hab⟩
  have : Std.Total r := ⟨fun e e' =>
    le_total (F.paramValue u e') (F.paramValue u e)⟩
  let order : List (Edge V) := F.edges.toList.mergeSort (r · ·)
  refine ⟨order, ?_, ?_⟩
  · exact (F.mem_edgeOrders_iff).mpr (List.mergeSort_perm F.edges.toList (r · ·))
  · rw [mem_orderedCubeSimplex_iff]
    constructor
    · exact hu
    · have hpair : order.Pairwise r := by
        exact List.pairwise_mergeSort' r F.edges.toList
      exact
        orderedSimplexParams_map_paramValue_of_pairwise_ge F u order 1
          hpair
          (by
            intro e he
            exact
              (F.paramValue_mem_Icc u ((mem_unitCube_iff F u).mp hu) e).1)
          (by
            intro e he
            exact
              (F.paramValue_mem_Icc u ((mem_unitCube_iff F u).mp hu) e).2)
end BKAR.Forest
