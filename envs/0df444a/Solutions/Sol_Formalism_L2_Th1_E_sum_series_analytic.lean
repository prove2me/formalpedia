-- Prove2me | solution 1 for Formalism.L2.Th1.E.sum_series_analytic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:31:55.067674+00:00
-- url     : https://prove2.me/submissions/8c23e890-11ef-4734-8435-e0a12859ce56

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Theorems.Thm_Formalism_L2_Th1_C_Dict_law_eq
import Theorems.Thm_Formalism_L2_Th1_C_Dict_subst_cob


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
theorem _root_.solution : SumEBridge := by
  intro K _ _ l linv hlp F hF hc ph ι _ N0 N1
  rw [Formalism.L2.Th1.C.Dict.law_eq hlp hF hc]
  unfold Formalism.L2.Th1.D.sumE beSum
  refine Finset.sum_congr rfl fun e => fun _ => ?_
  rw [← Formalism.L2.Th1.C.Dict.subst_cob hlp ph (MvPowerSeries.constantCoeff_X (false, e))
    (MvPowerSeries.constantCoeff_X (true, e))]
  congr 1
  funext a
  fin_cases a <;> rfl
end Formalism.L2.Th1.E
