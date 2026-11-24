-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.FrobStickLog_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:18.915371+00:00
-- url     : https://prove2.me/submissions/d0e5aac7-724d-4bfa-a990-6adb73ec2ce3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_sigS_cc
import Theorems.Thm_Formalism_L2_Th1_B_Fs_tau3
import Theorems.Thm_Formalism_L2_Th1_B_Fs_wp3_apply_eq_sq_mul_sub_sq_mul
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_three_eq_eval_last_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_formal_exp
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_det_three_points
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_vandermonde_three
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_exp_parallelogram
import Theorems.Thm_Formalism_L2_Th1_B_Fs_fsE_cc
import Theorems.Thm_Formalism_L2_Th1_B_Fs_X_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_weierstrass_pair_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_pd_two
import Theorems.Thm_Formalism_L2_Th1_B_Fs_D_vand3
import Theorems.Thm_Formalism_L2_Th1_B_Fs_D_fsE
import Theorems.Thm_Formalism_L2_Th1_B_Fs_ring_core
import Theorems.Thm_Formalism_L2_Th1_B_Add0_pd_two
import Theorems.Thm_Formalism_L2_Th1_B_Add0_ring_core
import Theorems.Thm_Formalism_L2_Th1_B_Add0_sigS_cc
import Theorems.Thm_Formalism_L2_Th1_B_pd_fExp
import Theorems.Thm_Formalism_L2_Th1_B_two_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Fs
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Formalism.L2.Th1.B.Fs
theorem _root_.solution (hS : ShearLemma) (hT : TauRule) (hD : DetRule) : FrobStickLog := by
  intro K _ _ g2 g3 P hP
  have cE : MvPowerSeries.constantCoeff (fsE (sigS P)) = 0 := fsE_cc (sigS_cc P)
  have two_ne : (2 : MvPowerSeries (Fin 3) K) ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this
    exact two_ne_zero this
  have hb : ev3H (-2 * vand3 K * fExp (fsE (sigS P))) =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1) * wp3 P 0 1 := by
    rw [map_mul, map_mul, map_neg, map_ofNat, eval_last_zero_vandermonde_three, eval_last_zero_formal_exp cE, eval_last_zero_exp_parallelogram (sigS_cc P),
      wp3_apply_eq_sq_mul_sub_sq_mul hP]
    ring
  refine hS K _ _ ?_ ?_ ?_
  · have hY : ∀ i : Fin 3, pd i (-2 * vand3 K * fExp (fsE (sigS P))) =
        -2 * (pd i (vand3 K) * fExp (fsE (sigS P)) +
          vand3 K * (fExp (fsE (sigS P)) * pd i (fsE (sigS P)))) := by
      intro i
      have h1 := pd_fExp i cE
      simp only [pd] at h1 ⊢
      rw [Derivation.leibniz, Derivation.leibniz, h1, map_neg, pd_two]
      simp only [smul_eq_mul]
      ring
    have core := ring_core (MvPowerSeries.X 0) (MvPowerSeries.X 1) (MvPowerSeries.X 2) _ _ _ _ _ _
      _ _ _ _ _ (tau3 hT hP (j := 0) (k := 1) (by decide)) (tau3 hT hP (j := 0) (k := 2) (by decide))
      (tau3 hT hP (j := 1) (k := 2) (by decide)) (hD K g2 g3 P hP)
    have hM : 2 * wp3 P 0 1 * wp3 P 0 2 * wp3 P 1 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne (weierstrass_pair_ne_zero hP (by decide)))
        (weierstrass_pair_ne_zero hP (by decide))) (weierstrass_pair_ne_zero hP (by decide))
    have core' := mul_left_cancel₀ hM core
    have hV : vand3 K = (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
      (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) *
      (MvPowerSeries.X 1 - MvPowerSeries.X 2) := rfl
    rw [← hV] at core'
    rw [hY, hY]
    linear_combination (-2 * fExp (fsE (sigS P))) * core' +
      (-2 * det3 P * fExp (fsE (sigS P))) * D_vand3 (K := K) +
      (-2 * det3 P * fExp (fsE (sigS P)) * vand3 K) * D_fsE (sigS P)
  · rw [eval_three_eq_eval_last_zero, eval_three_eq_eval_last_zero, hb, eval_last_zero_det_three_points]
  · rw [eval_three_eq_eval_last_zero, hb]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne)
      (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1))) (weierstrass_pair_ne_zero hP (by decide))
end Formalism.L2.Th1.B.Fs
