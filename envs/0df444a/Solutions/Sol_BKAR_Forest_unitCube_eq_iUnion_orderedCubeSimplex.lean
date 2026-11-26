-- Prove2me | solution 1 for BKAR.Forest.unitCube_eq_iUnion_orderedCubeSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:36.168488+00:00
-- url     : https://prove2.me/submissions/ddf21852-d457-4fd0-8f3f-485e9183e412

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral
import Theorems.Thm_BKAR_Forest_unitCube_subset_iUnion_orderedCubeSimplex
import Theorems.Thm_BKAR_Forest_iUnion_orderedCubeSimplex_subset_unitCube

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) :
    F.unitCube =
      ⋃ order : {order : List (Edge V) // order ∈ F.edgeOrders},
        F.orderedCubeSimplex order.val :=
  Set.Subset.antisymm
    (F.unitCube_subset_iUnion_orderedCubeSimplex)
    (F.iUnion_orderedCubeSimplex_subset_unitCube)
end BKAR.Forest
