-- Prove2me | solution 1 for Formalism.L2.Th1.F.Universal.isU_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:34:53.052027+00:00
-- url     : https://prove2.me/submissions/a6f8a81f-cd65-4552-8683-adcda3c42fcb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Universal
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_congr
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_const
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_mul
import Theorems.Thm_Formalism_L2_Th1_F_Universal_IsU_sum
import Theorems.Thm_Formalism_L2_Th1_F_Universal_isU_prim
import Theorems.Thm_Formalism_L2_Th1_F_Universal_coeff_exp_succ
import Theorems.Thm_Formalism_L2_Th1_F_Universal_coeff_exp_zero
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
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
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.F.Universal
theorem _root_.solution (n : ℕ) : IsU (fun K [Field K] [CharZero K] g2 g3 =>
    coeff n (B.fExp (B.sigS (pOf g2 g3)) : PowerSeries K)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · exact (isU_const 1).congr fun K _ _ g2 g3 => by rw [coeff_exp_zero]; simp
    · refine ((isU_const (1 / ((n : ℚ) + 1))).mul
        (IsU.sum (Finset.HasAntidiagonal.antidiagonal n) (fun ij K [Field K] [CharZero K] g2 g3 =>
          coeff ij.1 (-B.prim (pOf g2 g3)) *
            coeff ij.2 (B.fExp (B.sigS (pOf g2 g3)) : PowerSeries K))
          fun ij hij => (isU_prim ij.1).mul (ih ij.2 ?_))).congr
        fun K _ _ g2 g3 => coeff_exp_succ _ n
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      omega
end Formalism.L2.Th1.F.Universal
