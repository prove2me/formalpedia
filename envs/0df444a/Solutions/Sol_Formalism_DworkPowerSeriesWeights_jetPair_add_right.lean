-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:59.14626+00:00
-- url     : https://prove2.me/submissions/4550f10d-ad43-46f3-b6c4-25473316ecb5

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
theorem _root_.solution (P : MvPolynomial ι K) (F G : MvPowerSeries ι K) :
    jetPair P (F + G) = jetPair P F + jetPair P G := by
  simp only [jetPair, map_add, mul_add, Finset.sum_add_distrib]
end Formalism.DworkPowerSeriesWeights
