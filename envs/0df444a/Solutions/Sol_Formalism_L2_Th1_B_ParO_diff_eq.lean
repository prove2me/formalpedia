-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.diff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:05.157111+00:00
-- url     : https://prove2.me/submissions/314b91dd-fcef-4f8c-8722-94dfc7b943e3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_fLog_mul
import Theorems.Thm_Formalism_L2_Th1_B_ParO_psubst_fExp
import Theorems.Thm_Formalism_L2_Th1_B_ParO_X_mul_lU
import Theorems.Thm_Formalism_L2_Th1_B_ParO_constantCoeff_lU
import Theorems.Thm_Formalism_L2_Th1_B_ParO_psubst_C
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fExp
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_prim
import Theorems.Thm_Formalism_L2_Th1_B_fLog_fExp
import Theorems.Thm_Formalism_L2_Th1_B_psubst_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParO
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.ParO
theorem _root_.solution (hS : Sigma1Sq) {g2 g3 s2 c0 e1 : K} {P l ep : PowerSeries K}
    (hP : IsWp g2 g3 P) (he : 4 * e1 ^ 3 - g2 * e1 - g3 = 0)
    (hl0 : PowerSeries.constantCoeff l = 0) (hl1 : PowerSeries.coeff 1 l = 1)
    (h3 : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2)) :
    2 * (phE s2 e1 (3 * e1 ^ 2 - g2 / 4) (wOf e1 P) l - phO s2 P l) =
      -fLog (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) := by
  have hlS := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have hS1 : PowerSeries.constantCoeff
      (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P)) = 0 := by
    rw [Formalism.L2.Th1.B.sigmaOneSeries, map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]
  have hS0 : PowerSeries.constantCoeff (Formalism.L2.Th1.B.sigS P) = 0 := by
    rw [Formalism.L2.Th1.B.sigS, map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]
  have hsq := hS K g2 g3 e1 P hP he
  rw [Formalism.L2.Th1.B.sigma1, Formalism.L2.Th1.B.sigma] at hsq
  have hcan : Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P)) ^ 2 =
      Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.sigS P) ^ 2 *
        (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (PowerSeries.X_ne_zero (R := K)))
    linear_combination hsq
  have hsub := congrArg (fun φ : PowerSeries K => PowerSeries.subst l φ) hcan
  simp only [PowerSeries.subst_mul hlS, PowerSeries.subst_pow hlS, PowerSeries.subst_sub hlS,
    PowerSeries.subst_add hlS, Formalism.L2.Th1.B.psubst_one hlS, PowerSeries.subst_X hlS, psubst_C l,
    psubst_fExp (u := l) hl0 hS1, psubst_fExp (u := l) hl0 hS0] at hsub
  have hm : PowerSeries.X * Formalism.L2.Th1.B.lU l = l := X_mul_lU hl0
  have h3' : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      PowerSeries.X ^ 2 * (Formalism.L2.Th1.B.lU l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2)) := by
    linear_combination h3 -
      ((l + PowerSeries.X * Formalism.L2.Th1.B.lU l) * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2)) * hm
  have hQ := mul_left_cancel₀ (pow_ne_zero 2 (PowerSeries.X_ne_zero (R := K))) h3'
  have eq2 : Formalism.L2.Th1.B.fExp (PowerSeries.subst l
        (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P))) ^ 2 =
      Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) ^ 2 *
        (Formalism.L2.Th1.B.lU l ^ 2 * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)) := by
    rw [map_sub]
    linear_combination hsub + (Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) ^ 2) * hQ +
      (Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) ^ 2 * PowerSeries.C e1 *
        (l + PowerSeries.X * Formalism.L2.Th1.B.lU l)) * hm
  have hu : MvPowerSeries.constantCoeff (PowerSeries.subst l
      (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P))) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hl0 _ hS1
  have hv : MvPowerSeries.constantCoeff (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hl0 _ hS0
  have hEu := Formalism.L2.Th1.B.constantCoeff_fExp hu
  have hEv := Formalism.L2.Th1.B.constantCoeff_fExp hv
  have hm1 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l) = 1 := (constantCoeff_lU l).trans hl1
  have hE : MvPowerSeries.constantCoeff (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2) = 1 := by
    have h4 := congrArg (fun φ : PowerSeries K => MvPowerSeries.constantCoeff φ) eq2
    simp only [map_mul, map_pow, hEu, hEv, hm1, one_pow, one_mul] at h4
    exact h4.symm
  have hEvv : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) *
      Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P))) = 1 := by rw [map_mul, hEv, one_mul]
  have hmm : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l * Formalism.L2.Th1.B.lU l) = 1 := by rw [map_mul, hm1, one_mul]
  have hmmE : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l * Formalism.L2.Th1.B.lU l *
      (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)) = 1 := by rw [map_mul, hmm, hE, one_mul]
  have key : PowerSeries.subst l (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P)) +
        PowerSeries.subst l (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P)) =
      PowerSeries.subst l (Formalism.L2.Th1.B.sigS P) + PowerSeries.subst l (Formalism.L2.Th1.B.sigS P) +
        (Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU l) + Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU l) +
          Formalism.L2.Th1.B.fLog (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2)) :=
    calc _ = Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.fExp (PowerSeries.subst l
              (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P))) *
            Formalism.L2.Th1.B.fExp (PowerSeries.subst l
              (Formalism.L2.Th1.B.sigmaOneSeries e1 (3 * e1 ^ 2 - g2 / 4) (Formalism.L2.Th1.B.wOf e1 P)))) := by
          rw [fLog_mul hEu hEu, Formalism.L2.Th1.B.fLog_fExp hu]
      _ = Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) *
            Formalism.L2.Th1.B.fExp (PowerSeries.subst l (Formalism.L2.Th1.B.sigS P)) *
            (Formalism.L2.Th1.B.lU l * Formalism.L2.Th1.B.lU l * (ep + PowerSeries.C (c0 - e1) * PowerSeries.X ^ 2))) :=
          congrArg Formalism.L2.Th1.B.fLog (by linear_combination eq2)
      _ = _ := by
          rw [fLog_mul hEvv hmmE, fLog_mul hEv hEv, fLog_mul hmm hE, fLog_mul hm1 hm1,
            Formalism.L2.Th1.B.fLog_fExp hv]
  rw [Formalism.L2.Th1.B.phE, Formalism.L2.Th1.B.phO]
  linear_combination (-1 : PowerSeries K) * key
end Formalism.L2.Th1.B.ParO
