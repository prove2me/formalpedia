-- Prove2me | solution 1 for BKAR.Forest.orderedSectorSum_eq_sum_orderTails_of_edges_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:30:07.024632+00:00
-- url     : https://prove2.me/submissions/436396f0-a6ec-40ff-a049-ba66d78acfff

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_orderedSectorSum_eq_sum_cons_of_edges_nonempty

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
      Finset.sum (edgeSetOrderTails F.edges)
        (fun x => F.orderedContribution (x.1.val :: x.2) ρ) := by
  rw [F.orderedSectorSum_eq_sum_cons_of_edges_nonempty hF ρ]
  rw [edgeSetOrderTails, Finset.sum_sigma]
end BKAR.Forest
