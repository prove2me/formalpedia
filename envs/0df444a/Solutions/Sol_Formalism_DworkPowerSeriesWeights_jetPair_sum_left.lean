-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:11.555608+00:00
-- url     : https://prove2.me/submissions/7b4105e7-79ae-4357-a4e0-27e404487d83

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_add_left
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_zero_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι : Type}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {α : Type*} (s : Finset α) (P : α → MvPolynomial ι K)
    (F : MvPowerSeries ι K) : jetPair (∑ a ∈ s, P a) F = ∑ a ∈ s, jetPair (P a) F := by
  classical
  refine Finset.induction_on s (by simp [jetPair_zero_left]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, jetPair_add_left, ih]
end Formalism.DworkPowerSeriesWeights
