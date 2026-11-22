-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:24.052603+00:00
-- url     : https://prove2.me/submissions/b903e583-fd62-4e5c-b1ab-58b899e953ec

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP

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
theorem _root_.solution {α : Type*} (s : Finset α) (P : MvPolynomial ι K)
    (F : α → MvPowerSeries ι K) : jetPair P (∑ a ∈ s, F a) = ∑ a ∈ s, jetPair P (F a) := by
  simp only [jetPair, map_sum, Finset.mul_sum]
  exact Finset.sum_comm
end Formalism.DworkPowerSeriesWeights
