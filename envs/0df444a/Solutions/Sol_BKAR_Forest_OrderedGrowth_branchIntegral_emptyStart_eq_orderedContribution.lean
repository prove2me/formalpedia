-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.branchIntegral_emptyStart_eq_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:43.007019+00:00
-- url     : https://prove2.me/submissions/06fd91a5-0593-4084-8c2c-5d31a238054c

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def_standardInterp
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_emptyStart_eq_paramsOfOrder_of_length
import Theorems.Thm_BKAR_orderedSimplexIntegral_congr_of_length


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {G : Forest V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution
    (growth : OrderedGrowth (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    growth.branchIntegral emptyParam ρ =
      G.orderedContribution order ρ := by
  rw [branchIntegral, branchIntegralAux, orderedContribution]
  apply orderedSimplexIntegral_congr_of_length
  intro ts hlen
  rw [branchIntegrand_def_standardInterp]
  rw [growth.params_emptyStart_eq_paramsOfOrder_of_length hlen]
end BKAR.Forest.OrderedGrowth
