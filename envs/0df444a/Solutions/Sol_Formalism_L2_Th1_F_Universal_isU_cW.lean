-- Prove2me | solution 1 for Formalism.L2.Th1.F.Universal.isU_cW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:15.685835+00:00
-- url     : https://prove2.me/submissions/73e10c2e-8dc9-4216-91db-96ecffa46f84

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_congr
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_const
import Theorems.Thm_Formalism_L2_Th1_F_Universal_universal_g2
import Theorems.Thm_Formalism_L2_Th1_F_Universal_universal_g3
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_mul
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_sum
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_L2_Th1_F_POf_cW_eq
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul


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
theorem _root_.solution (k : ℕ) : IsU (fun K [Field K] [CharZero K] g2 g3 => cW g2 g3 k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h2 : k = 2
    · refine (universal_g2.mul (isU_const (1 / 20))).congr fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_pos h2]
      push_cast
      ring
    by_cases h3 : k = 3
    · refine (universal_g3.mul (isU_const (1 / 28))).congr fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_neg h2, if_pos h3]
      push_cast
      ring
    by_cases h4 : 4 ≤ k
    · refine ((isU_const (3 / ((2 * (k : ℚ) + 1) * ((k : ℚ) - 3)))).mul
        (IsU.sum Finset.univ (fun (m : Fin (k - 3)) K [Field K] [CharZero K] g2 g3 =>
          cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2)))
          fun m _ => (ih (m.val + 2) (by omega)).mul (ih (k - (m.val + 2)) (by omega)))).congr
        fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_neg h2, if_neg h3, if_pos h4]
      push_cast
      rfl
    · refine (isU_const 0).congr fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_neg h2, if_neg h3, if_neg h4]
      simp
end Formalism.L2.Th1.F.Universal
