-- Prove2me | solution 1 for BKAR.Forest.paramsOfOrder_continuous_of_listPathContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:12:39.811623+00:00
-- url     : https://prove2.me/submissions/a7ea81c9-315c-482f-8116-16fe05e4c409

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_CubePartition_Smoothness

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (order : List (Edge V))
    {X : Type*} [TopologicalSpace X] {n : Nat} {tsPath : X → List ℝ}
    (hts : BKAR.ListPathContinuous n tsPath) :
    Continuous (fun x : X => F.paramsOfOrder order (tsPath x)) := by
  apply continuous_pi
  intro e
  exact hts.2 (order.idxOf e.val)
end BKAR.Forest
