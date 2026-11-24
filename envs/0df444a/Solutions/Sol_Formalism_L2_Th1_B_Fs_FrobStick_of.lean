-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.FrobStick_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:12.234828+00:00
-- url     : https://prove2.me/submissions/3fe23a5b-f02a-4f25-894e-03d32aa1c61a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_cc_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Fs_sigS_cc
import Theorems.Thm_Formalism_L2_Th1_B_Fs_subst_sigma
import Theorems.Thm_Formalism_L2_Th1_B_Fs_fsE_cc
import Theorems.Thm_Formalism_L2_Th1_B_Fs_fExp_three
import Theorems.Thm_Formalism_L2_Th1_B_Add0_sigS_cc
import Theorems.Thm_Formalism_L2_Th1_B_Add0_subst_sigma
import Theorems.Thm_Formalism_L2_Th1_B_Add1_cc_psubst
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add


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
theorem _root_.solution (hL : FrobStickLog) : FrobStick := by
  intro K _ _ g2 g3 P hP
  have h := hL K g2 g3 P hP
  have c0 : ∀ x : Fin 3, MvPowerSeries.constantCoeff
      (at1 x (sigS P) : MvPowerSeries (Fin 3) K) = 0 := fun x => cc_psubst (by simp) (sigS_cc P)
  have c3 : ∀ x : Fin 3, MvPowerSeries.constantCoeff
      (3 * at1 x (sigS P) : MvPowerSeries (Fin 3) K) = 0 := fun x => by rw [map_mul, c0, mul_zero]
  have cS : MvPowerSeries.constantCoeff (evalSumThree (sigS P)) = 0 := cc_psubst (by simp) (sigS_cc P)
  have cD : ∀ j k : Fin 3, MvPowerSeries.constantCoeff (evalDiffThree j k (sigS P)) = 0 :=
    fun j k => cc_psubst (by simp) (sigS_cc P)
  have cE : MvPowerSeries.constantCoeff (fsE (sigS P)) = 0 := fsE_cc (sigS_cc P)
  have key : fExp (at1 0 (sigS P)) ^ 3 * fExp (at1 1 (sigS P)) ^ 3 * fExp (at1 2 (sigS P)) ^ 3 *
        fExp (fsE (sigS P)) =
      fExp (evalSumThree (sigS P)) * fExp (evalDiffThree 0 1 (sigS P)) * fExp (evalDiffThree 0 2 (sigS P)) *
        fExp (evalDiffThree 1 2 (sigS P)) := by
    rw [fExp_three (c0 0), fExp_three (c0 1), fExp_three (c0 2), ← fExp_add (c3 0) (c3 1),
      ← fExp_add (by rw [map_add, c3, c3, add_zero]) (c3 2),
      ← fExp_add (by rw [map_add, map_add, c3, c3, c3, add_zero, add_zero]) cE,
      ← fExp_add cS (cD 0 1), ← fExp_add (by rw [map_add, cS, cD, add_zero]) (cD 0 2),
      ← fExp_add (by rw [map_add, map_add, cS, cD, cD, add_zero, add_zero]) (cD 1 2)]
    congr 1
    rw [fsE]
    ring
  have eS : evalSumThree (sigma P) = (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
      fExp (evalSumThree (sigS P)) := subst_sigma P (by simp)
  have eD : ∀ j k : Fin 3, evalDiffThree j k (sigma P) = (MvPowerSeries.X j - MvPowerSeries.X k) *
      fExp (evalDiffThree j k (sigS P)) := fun j k => subst_sigma P (by simp)
  have e0 : ∀ x : Fin 3, (at1 x (sigma P) : MvPowerSeries (Fin 3) K) =
      MvPowerSeries.X x * fExp (at1 x (sigS P)) := fun x => subst_sigma P (by simp)
  rw [eS, eD, eD, eD, e0, e0, e0, h, vand3]
  linear_combination
    (-2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
        (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) *
        (MvPowerSeries.X 1 - MvPowerSeries.X 2))) * key
end Formalism.L2.Th1.B.Fs
