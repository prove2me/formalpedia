-- Prove2me | solution 1 for Formalism.L2.Th1.E.product_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:00:02.181812+00:00
-- url     : https://prove2.me/submissions/9d141759-bd9f-4c2c-bf26-7c89d6f56b3c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_series_at_variable_mul
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_series_at_variable_neg
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_intMv_thetaProd
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_integral_iff
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_intS_iff
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_mem_ball
import Theorems.Thm_Formalism_ELL_VeluIntegrality_mem_ball
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_sum
import Theorems.Thm_Formalism_L2_Th1_C_subst_mvExp


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
theorem _root_.solution : ProdInt := by
  intro K _ _ _ κ n _ _ ph r V hph hr hV
  refine ⟨?_, (integral_iff mem_ball _).2 (intMv_thetaProd (fun k => (mem_ball _).2 (hr k))
    fun k i => (intS_iff mem_ball _).1 (hV k i))⟩
  have hnph : PowerSeries.constantCoeff (-ph) = 0 := by rw [map_neg, hph, neg_zero]
  have hE : ∀ i : n, at1 i (mvExp (-ph) : PowerSeries K) = mvExp (-(at1 i ph)) := by
    intro i
    rw [← series_at_variable_neg]
    exact Formalism.L2.Th1.C.subst_mvExp hnph (MvPowerSeries.constantCoeff_X i)
  have hS : mvExp (-(phSum ph : MvPowerSeries n K)) = ∏ i : n, mvExp (-(at1 i ph)) := by
    unfold phSum
    rw [← Finset.sum_neg_distrib]
    exact Formalism.L2.Th1.C.mvExp_sum _ _ fun i _ => by rw [map_neg, constantCoeff_inVar_eq_zero i hph, neg_zero]
  unfold thetaProd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hS, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [series_at_variable_mul, hE]
end Formalism.L2.Th1.E
