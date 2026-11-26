-- Prove2me | solution 1 for BKAR.Forest.paramsOfOrder_cons_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:36.663814+00:00
-- url     : https://prove2.me/submissions/12a07029-1bef-441a-bdb2-8afcb98f23ff

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
    (e : Edge V) (order : List (Edge V)) (t : ℝ) (ts : List ℝ)
    (he : e ∈ F.edges) :
    F.paramsOfOrder (e :: order) (t :: ts) ⟨e, he⟩ = t := by
  rw [paramsOfOrder]
  change (t :: ts).getD ((e :: order).idxOf e) 0 = t
  rw [List.idxOf_cons_self]
  rfl
end BKAR.Forest
