-- Prove2me | solution 1 for Formalism.L2.Th1.E.map_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:59.680808+00:00
-- url     : https://prove2.me/submissions/3b3b11a6-4e23-4ae4-b869-54cc7aa66abb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_cob


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq cob IsLawOfLog lgF UnrOK)
open Formalism.L2.Th1.C (IntMv IntPS IsPt)
open CompatibleChartOperations
namespace Formalism.L2.Th1.E
theorem _root_.solution : MapCob := by
  intro K0 K _ _ j F f hF
  exact Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_cob j F hF f
end Formalism.L2.Th1.E
