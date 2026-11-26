-- Prove2me | solution 1 for BKAR.Forest.paramsOfOrder_cons_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:42.623535+00:00
-- url     : https://prove2.me/submissions/793dfc62-605c-4fa5-a195-c87cc1de4a75

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    {e e' : Edge V} (order : List (Edge V)) (t : ℝ) (ts : List ℝ)
    (he' : e' ∈ F.edges) (hne : e' ≠ e) :
    F.paramsOfOrder (e :: order) (t :: ts) ⟨e', he'⟩ =
      ts.getD (order.idxOf e') 0 := by
  rw [paramsOfOrder]
  change (t :: ts).getD ((e :: order).idxOf e') 0 =
    ts.getD (order.idxOf e') 0
  rw [List.idxOf_cons_ne order (fun h => hne h.symm)]
  rfl
end BKAR.Forest
