-- Prove2me | solution 1 for BKAR.Forest.orderedSectorSum_eq_sum_cons_of_edges_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:29:02.292191+00:00
-- url     : https://prove2.me/submissions/48fdc68b-5b9c-486d-9bce-acb8ab82aab8

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_sum_edgeOrders_eq_sum_cons_of_edges_nonempty

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F : Forest V) (hF : F.edges.Nonempty)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedSectorSum ρ =
      Finset.sum F.edges.attach
        (fun e => Finset.sum (edgeSetOrders (F.edges.erase e.val))
          (fun order => F.orderedContribution (e.val :: order) ρ)) := by
  rw [orderedSectorSum]
  exact F.sum_edgeOrders_eq_sum_cons_of_edges_nonempty hF
    (fun order => F.orderedContribution order ρ)
end BKAR.Forest
