-- Prove2me | solution 1 for BKAR.Forest.mem_orderedCubeSimplex_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:48:39.952351+00:00
-- url     : https://prove2.me/submissions/7af72d29-5863-4225-ac5c-30f286115e8a

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
    (F : Forest V) (order : List (Edge V)) (u : F.EdgeParam → ℝ) :
    u ∈ F.orderedCubeSimplex order ↔
      u ∈ F.unitCube ∧
        OrderedSimplexParams 1 (order.map (F.paramValue u)) :=
  Iff.rfl
end BKAR.Forest
