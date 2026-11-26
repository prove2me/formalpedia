-- Prove2me | solution 1 for BKAR.Forest.iUnion_orderedCubeSimplex_subset_unitCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:22.579375+00:00
-- url     : https://prove2.me/submissions/a73b098d-603f-4b8f-bbb1-08eeeb640d91

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Theorems.Thm_BKAR_Forest_orderedCubeSimplex_subset_unitCube

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) :
    (⋃ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        F.orderedCubeSimplex order.val) ⊆ F.unitCube := by
  intro u hu
  rw [Set.mem_iUnion] at hu
  rcases hu with ⟨order, hsector⟩
  exact F.orderedCubeSimplex_subset_unitCube order.val hsector
end BKAR.Forest
