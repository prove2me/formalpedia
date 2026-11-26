-- Prove2me | solution 1 for BKAR.Forest.orderedCubeSimplex_subset_unitCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:56:20.113823+00:00
-- url     : https://prove2.me/submissions/d3516dcd-a405-4262-a682-c0ae057f49d9

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_CubeIntegral

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (order : List (Edge V)) :
    F.orderedCubeSimplex order ⊆ F.unitCube := by
  intro u hu
  exact hu.1
end BKAR.Forest
