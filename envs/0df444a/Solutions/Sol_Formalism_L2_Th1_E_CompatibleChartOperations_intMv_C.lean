-- Prove2me | solution 1 for Formalism.L2.Th1.E.CompatibleChartOperations.intMv_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:03.607576+00:00
-- url     : https://prove2.me/submissions/02bdb1ca-9ad1-468e-9067-0be5a009d1a8

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
theorem _root_.solution {a : K} (ha : a ∈ R) : IntMv R (MvPowerSeries.C a : MvPowerSeries σ K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact R.zero_mem
end Formalism.L2.Th1.E.CompatibleChartOperations
