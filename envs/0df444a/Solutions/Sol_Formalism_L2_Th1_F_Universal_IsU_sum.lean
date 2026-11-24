-- Prove2me | solution 1 for Formalism.L2.Th1.F.Universal.IsU.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:56.77019+00:00
-- url     : https://prove2.me/submissions/56f79d4e-d211-4569-8185-bdade25537aa

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_congr
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_const
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_add
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add


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
open Formalism.L2.Th1.CM (cW)
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Universal
namespace Formalism.L2.Th1.F.Universal
namespace IsU
theorem _root_.solution {ι : Type} (s : Finset ι) (a : ι → ∀ (K : Type) [Field K] [CharZero K], K → K → K)
    (h : ∀ i ∈ s, IsU (a i)) :
    IsU (fun K [Field K] [CharZero K] g2 g3 => ∑ i ∈ s, a i K g2 g3) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isU_const 0).congr fun K _ _ g2 g3 => by simp
  | insert i s hi ih =>
    refine ((h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr fun K _ _ g2 g3 => ?_
    rw [Finset.sum_insert hi]
end IsU
end Formalism.L2.Th1.F.Universal
