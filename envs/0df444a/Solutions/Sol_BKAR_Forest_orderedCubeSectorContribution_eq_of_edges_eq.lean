-- Prove2me | solution 1 for BKAR.Forest.orderedCubeSectorContribution_eq_of_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:06.951802+00:00
-- url     : https://prove2.me/submissions/b7c45d1c-1b95-41db-b1d8-2ead943fbcf4

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_measurableSet_orderedFinSimplex
import Theorems.Thm_BKAR_Forest_orderedCubeSectorContribution_eq_orderedFinSimplexIntegral
import Theorems.Thm_BKAR_Forest_paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm
import Theorems.Thm_BKAR_Forest_standardInterp_paramsOfOrder_eq_of_edges_eq


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F G : Forest V) (hedges : F.edges = G.edges)
    {order : List (Edge V)}
    (hForder : order ∈ F.edgeOrders) (hGorder : order ∈ G.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedCubeSectorContribution order ρ =
      G.orderedCubeSectorContribution order ρ := by
  rw [F.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral hForder ρ]
  rw [G.orderedCubeSectorContribution_eq_orderedFinSimplexIntegral hGorder ρ]
  apply setIntegral_congr_fun (measurableSet_orderedFinSimplex order.length)
  intro ts _hts
  apply congrArg (mixedPartialList order.reverse ρ)
  rw [← F.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm hForder ts]
  rw [← G.paramsOfOrder_ofFn_eq_orderMeasurableEquiv_symm hGorder ts]
  exact F.standardInterp_paramsOfOrder_eq_of_edges_eq G hedges
    order (List.ofFn ts)
end BKAR.Forest
