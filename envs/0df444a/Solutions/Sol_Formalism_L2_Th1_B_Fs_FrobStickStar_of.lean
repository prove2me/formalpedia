-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.FrobStickStar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:11.2738+00:00
-- url     : https://prove2.me/submissions/a7e0d8a7-a24d-4573-910a-086988fb47b1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_subst_sgStar
import Theorems.Thm_Formalism_L2_Th1_B_Fs_fExp_three
import Theorems.Thm_Formalism_L2_Th1_B_Add0_subst_sgStar
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
theorem _root_.solution (hF : FrobStick) : FrobStickStar := by
  intro K _ _ g2 g3 s2 P hP
  have h := hF K g2 g3 P hP
  have cc : ∀ u : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff u = 0 →
      MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * u ^ 2)) = 0 := by
    intro u hu; simp [hu]
  have z : ∀ x : Fin 3, MvPowerSeries.constantCoeff
      (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X x : MvPowerSeries (Fin 3) K) ^ 2)) = 0 :=
    fun x => cc _ (by simp)
  have z3 : ∀ x : Fin 3, MvPowerSeries.constantCoeff
      (3 * -(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X x : MvPowerSeries (Fin 3) K) ^ 2)) = 0 :=
    fun x => by rw [map_mul, z, mul_zero]
  have zS := cc (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) (by simp)
  have zD : ∀ j k : Fin 3, MvPowerSeries.constantCoeff
      (-(MvPowerSeries.C (s2 / 2) *
        (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K) ^ 2)) = 0 :=
    fun j k => cc _ (by simp)
  have key : (fExp (-(MvPowerSeries.C (s2 / 2) *
          (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * MvPowerSeries.X 1 ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * MvPowerSeries.X 2 ^ 2))) ^ 3 =
      fExp (-(MvPowerSeries.C (s2 / 2) *
          (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2) ^ 2)) := by
    rw [mul_pow, mul_pow, fExp_three (z 0), fExp_three (z 1), fExp_three (z 2),
      ← fExp_add (z3 0) (z3 1), ← fExp_add (by rw [map_add, z3, z3, add_zero]) (z3 2),
      ← fExp_add zS (zD 0 1), ← fExp_add (by rw [map_add, zS, zD, add_zero]) (zD 0 2),
      ← fExp_add (by rw [map_add, map_add, zS, zD, zD, add_zero, add_zero]) (zD 1 2)]
    congr 1
    ring
  have eS : evalSumThree (sgStar s2 P) = evalSumThree (sigma P) * _ := subst_sgStar s2 P (by simp)
  have eD : ∀ j k : Fin 3, evalDiffThree j k (sgStar s2 P) = evalDiffThree j k (sigma P) * _ :=
    fun j k => subst_sgStar s2 P (by simp)
  have e0 : ∀ x : Fin 3, (at1 x (sgStar s2 P) : MvPowerSeries (Fin 3) K) = at1 x (sigma P) * _ :=
    fun x => subst_sgStar s2 P (by simp)
  rw [eS, eD, eD, eD, e0, e0, e0]
  linear_combination
    ((fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * MvPowerSeries.X 1 ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * MvPowerSeries.X 2 ^ 2))) ^ 3) * h +
    (-2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
      (evalSumThree (sigma P) * evalDiffThree 0 1 (sigma P) * evalDiffThree 0 2 (sigma P) * evalDiffThree 1 2 (sigma P))) * key
end Formalism.L2.Th1.B.Fs
