-- Prove2me | solution 1 for BKAR.Forest.unitCube_subset_iUnion_orderedCubeSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:34.294282+00:00
-- url     : https://prove2.me/submissions/87745965-3ded-498a-8088-58843da5679e

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Theorems.Thm_BKAR_Forest_exists_mem_edgeOrders_and_mem_orderedCubeSimplex_of_mem_unitCube

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) :
    F.unitCube ⊆
      ⋃ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        F.orderedCubeSimplex order.val := by
  intro u hu
  rcases F.exists_mem_edgeOrders_and_mem_orderedCubeSimplex_of_mem_unitCube
      hu with
    ⟨order, horder, hsector⟩
  rw [Set.mem_iUnion]
  exact ⟨⟨order, horder⟩, hsector⟩
end BKAR.Forest
