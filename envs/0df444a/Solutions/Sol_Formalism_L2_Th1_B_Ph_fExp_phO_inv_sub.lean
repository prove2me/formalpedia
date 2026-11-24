-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.fExp_phO_inv_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:49:34.679265+00:00
-- url     : https://prove2.me/submissions/105c5f42-25a9-47b5-8e09-24795cab3c3a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Ph_X_mul_lU
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_lU
import Theorems.Thm_Formalism_L2_Th1_B_Ph_phO_inv_sub
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fLog
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add
import Theorems.Thm_Formalism_L2_Th1_B_fExp_fLog


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Ph
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Ph
theorem _root_.solution (s2 : K) {P l i : PowerSeries K} (hP : ∀ n, Odd n → coeff n P = 0)
    (hl : constantCoeff l = 0) (hl1 : coeff 1 l = 1) (hi : constantCoeff i = 0)
    (hli : subst i l = -l) :
    fExp (subst i (phO s2 P l) - phO s2 P l) = -lU i := by
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rw [hl1] at this
    exact this
  have hblu : MvPowerSeries.constantCoeff (subst i (lU l)) = 1 := by
    have := constantCoeff_psubst hi (lU l)
    exact this.trans hlu
  have hA : MvPowerSeries.constantCoeff (fLog (lU l)) = 0 := constantCoeff_fLog hlu
  have hB : MvPowerSeries.constantCoeff (fLog (subst i (lU l))) = 0 := constantCoeff_fLog hblu
  have hAB : MvPowerSeries.constantCoeff (fLog (lU l) - fLog (subst i (lU l))) = 0 := by
    rw [map_sub, hA, hB, sub_zero]
  rw [phO_inv_sub s2 hP hl hl1 hi hli]
  have hb0 : subst i (lU l) ≠ 0 := by
    intro h
    rw [h, map_zero] at hblu
    exact zero_ne_one hblu
  have key1 : fExp (fLog (lU l) - fLog (subst i (lU l))) * subst i (lU l) = lU l := by
    calc fExp (fLog (lU l) - fLog (subst i (lU l))) * subst i (lU l)
        = fExp (fLog (lU l) - fLog (subst i (lU l))) * fExp (fLog (subst i (lU l))) := by
          rw [fExp_fLog hblu]
      _ = fExp (fLog (lU l) - fLog (subst i (lU l)) + fLog (subst i (lU l))) := (fExp_add hAB hB).symm
      _ = lU l := by rw [sub_add_cancel, fExp_fLog hlu]
  have h1 : subst i (X * lU l) = subst i l := by rw [X_mul_lU hl]
  rw [subst_mul (hs hi), subst_X (hs hi), hli] at h1
  have key2 : -lU i * subst i (lU l) = lU l := by
    have h2 : X * (-lU i * subst i (lU l)) = X * lU l := by
      calc X * (-lU i * subst i (lU l)) = -((X * lU i) * subst i (lU l)) := by ring
        _ = -(i * subst i (lU l)) := by rw [X_mul_lU hi]
        _ = X * lU l := by rw [h1, neg_neg, X_mul_lU hl]
    exact mul_left_cancel₀ X_ne_zero h2
  apply mul_right_cancel₀ hb0
  rw [key1, key2]
end Formalism.L2.Th1.B.Ph
