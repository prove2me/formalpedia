-- Prove2me | solution 1 for Formalism.L2.Th1.E.CompatibleChartOperations.intMv_thetaProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:38:54.486168+00:00
-- url     : https://prove2.me/submissions/1f65173b-d6ac-46e1-b3b5-59559a7c9314

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_intMv_C
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_intMv_sum
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_isPt_X
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_mul
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_prod
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_X


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
theorem _root_.solution {κ : Type} [Fintype κ] [Fintype σ] {r : κ → K} {V : κ → σ → PowerSeries K}
    (hr : ∀ k, r k ∈ R) (hV : ∀ k i, IntPS R (V k i)) : IntMv R (thetaProd r V) :=
  intMv_sum _ fun k _ => Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_mul (intMv_C (hr k))
    (Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_prod _ fun i _ => Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_subst (hV k i) (isPt_X i))
end Formalism.L2.Th1.E.CompatibleChartOperations
