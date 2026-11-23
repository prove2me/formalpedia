-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_one_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:53.537594+00:00
-- url     : https://prove2.me/submissions/3992c0c8-6404-4feb-8b00-21075bc61161

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_left


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
variable {K : Type u} [Field K] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (F : MvPowerSeries ι K) :
    jetPair (1 : MvPolynomial ι K) F = MvPowerSeries.constantCoeff F := by
  rw [← MvPolynomial.C_1, jetPair_C_left, one_mul]
end Formalism.DworkPowerSeriesWeights
