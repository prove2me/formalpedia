-- Prove2me | solution 1 for Formalism.L2.Th1.E.CompatibleChartOperations.series_at_variable_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:36:52.540314+00:00
-- url     : https://prove2.me/submissions/5811b455-3e08-47e8-ace3-ee6c2fadb2b0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero

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
open Formalism.L2.Th1.E.CompatibleChartOperations
variable {K : Type} [Field K] {σ : Type} {R : Subring K}
namespace Formalism.L2.Th1.E.CompatibleChartOperations
theorem _root_.solution (i : σ) (f g : PowerSeries K) : at1 i (f * g) = at1 i f * at1 i g :=
  PowerSeries.subst_mul (PowerSeries.HasSubst.X i) f g
end Formalism.L2.Th1.E.CompatibleChartOperations
