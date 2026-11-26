-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.singletonGrowth_branchIntegral_empty_eq_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:41.697472+00:00
-- url     : https://prove2.me/submissions/5b626b87-9ea8-4962-ba09-8a6e3b3c85cf

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_empty_eq_paramsOfOrder_singleton
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_cons_nil_eq_integral_partialDeriv_standardInterp
import Theorems.Thm_BKAR_orderedSimplexIntegral_singleton


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {e : Edge V}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution
    (h : ActiveExtension (Forest.empty V) e)
    (ρ : (Edge V → ℝ) → ℝ) :
    h.singletonGrowth.branchIntegral emptyParam ρ =
      h.forest.orderedContribution [e] ρ := by
  rw [singletonGrowth]
  rw [OrderedGrowth.branchIntegral_cons_nil_eq_integral_partialDeriv_standardInterp]
  rw [orderedContribution, orderedSimplexIntegral_singleton]
  apply intervalIntegral.integral_congr
  intro t _
  change partialDeriv e ρ
      (h.forest.standardInterp (h.extension.extendParam emptyParam t)) =
    partialDeriv e ρ
      (h.forest.standardInterp (h.forest.paramsOfOrder [e] [t]))
  rw [h.extension.extendParam_empty_eq_paramsOfOrder_singleton t]
end BKAR.Forest.ActiveExtension
