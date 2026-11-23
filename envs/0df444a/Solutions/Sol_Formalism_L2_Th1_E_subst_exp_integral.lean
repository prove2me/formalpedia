-- Prove2me | solution 1 for Formalism.L2.Th1.E.subst_exp_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:26.937797+00:00
-- url     : https://prove2.me/submissions/0ea183a1-a851-4e6d-897e-1fab745fb31b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_integral_iff
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_mem_ball
import Theorems.Thm_Formalism_ELL_VeluIntegrality_mem_ball
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_substMv
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_substMv_mvExp


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
theorem _root_.solution : SubstExpInt := by
  intro K _ _ _ n m _ φ hφ0 hφ Φ U hΦ hU
  have h := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have hnΦ : MvPowerSeries.constantCoeff (-Φ) = 0 := by rw [map_neg, hΦ, neg_zero]
  refine ⟨?_, ?_, MvPowerSeries.constantCoeff_subst_eq_zero h hφ0 hΦ⟩
  · have hneg : MvPowerSeries.subst φ (-Φ) = -MvPowerSeries.subst φ Φ := by
      rw [← MvPowerSeries.coe_substAlgHom h, map_neg]
    rw [MvPowerSeries.subst_mul h, ← hneg]
    congr 1
    exact Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp hnΦ hφ0
  · exact (integral_iff mem_ball _).2 (Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.intMv_substMv ((integral_iff mem_ball _).1 hU)
      fun i => ⟨hφ0 i, (integral_iff mem_ball _).1 (hφ i)⟩)
end Formalism.L2.Th1.E
