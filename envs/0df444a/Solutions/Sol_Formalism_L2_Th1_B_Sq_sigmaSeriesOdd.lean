-- Prove2me | solution 1 for Formalism.L2.Th1.B.Sq.sigmaSeriesOdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:13.917704+00:00
-- url     : https://prove2.me/submissions/0abd3524-6657-48b5-8185-7f22879630cd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Theorems.Thm_Formalism_L2_Th1_B_Sq_fExp_even
import Theorems.Thm_Formalism_L2_Th1_B_Sq_prim_prim_even
import Theorems.Thm_Formalism_L2_Th1_B_Sq_constantCoeff_sigS
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Sq
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Sq
theorem _root_.solution : SigmaOdd := by
  intro K _ _ P hP
  have hs : ∀ n, Odd n → coeff n (sigS P) = 0 := by
    intro n hn
    rw [sigS, map_neg, prim_prim_even hP n hn, neg_zero]
  have he := fExp_even (constantCoeff_sigS P) hs
  have h0 : PowerSeries.constantCoeff (fExp (sigS P) : PowerSeries K) = 1 :=
    constantCoeff_fExp (constantCoeff_sigS P)
  constructor
  · have h1 := PowerSeries.coeff_succ_X_mul 0 (fExp (sigS P) : PowerSeries K)
    simp only [zero_add] at h1
    rw [sigma, h1, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  · intro n hn
    rcases n with _ | m
    · simp [sigma]
    · rw [sigma, PowerSeries.coeff_succ_X_mul]
      exact he m (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn))
end Formalism.L2.Th1.B.Sq
