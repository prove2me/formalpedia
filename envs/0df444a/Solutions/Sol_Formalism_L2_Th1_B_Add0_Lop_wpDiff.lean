-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.Lop_wpDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:31.033287+00:00
-- url     : https://prove2.me/submissions/c7bd10c4-9616-450e-87e5-3a69bbd64ed5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_triple_lintegral_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add0_ring_core
import Theorems.Thm_Formalism_L2_Th1_B_Add0_pderiv_zero_weierstrass_difference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_pderiv_one_weierstrass_difference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_pderiv_zero_zero_weierstrass_difference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_pderiv_one_one_weierstrass_difference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_series_at_variable_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]
local notation "A2" => MvPowerSeries (Fin 2) K
namespace Formalism.L2.Th1.B.Add0
theorem _root_.solution (h8 : WpReduced) {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) :
    Lop (wpDiff P) = (2 * at1 0 P - 2 * at1 1 P) * wpDiff P ^ 2 := by
  obtain ⟨hA, hB⟩ := h8 K g2 g3 P hP
  have hX : ∀ x : Fin 2, (at1 x PowerSeries.X : A2) = MvPowerSeries.X x := fun x =>
    PowerSeries.subst_X (PowerSeries.HasSubst.X x)
  have T : ∀ (x : Fin 2) (F : PowerSeries K),
      PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := K) x) F = (at1 x F : A2) :=
    fun x F => (triple_lintegral_eq x F).symm
  have hC : (MvPowerSeries.C g2 : A2) = 2 * MvPowerSeries.C (g2 / 2) := by
    have e : g2 = 2 * (g2 / 2) := by ring
    conv_lhs => rw [e]
    rw [map_mul, map_ofNat]
  have F1 : ∀ x : Fin 2, (MvPowerSeries.X x) ^ 4 * (at1 x (dz P)) ^ 2 - 4 * MvPowerSeries.X x * at1 x (dz P) =
      12 * at1 x P + 12 * (MvPowerSeries.X x) ^ 2 * (at1 x P) ^ 2 + 4 * (MvPowerSeries.X x) ^ 4 * (at1 x P) ^ 3 -
        MvPowerSeries.C g2 * (MvPowerSeries.X x) ^ 2 * (1 + (MvPowerSeries.X x) ^ 2 * at1 x P) -
        MvPowerSeries.C g3 * (MvPowerSeries.X x) ^ 4 := by
    intro x
    have := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := K) x)) hA
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one] at this
    simp only [T, hX, series_at_variable_const] at this
    exact this
  have F2 : ∀ x : Fin 2, (MvPowerSeries.X x) ^ 2 * at1 x (dz (dz P)) =
      12 * at1 x P + 6 * (MvPowerSeries.X x) ^ 2 * (at1 x P) ^ 2 -
        MvPowerSeries.C (g2 / 2) * (MvPowerSeries.X x) ^ 2 := by
    intro x
    have := congrArg (PowerSeries.substAlgHom (PowerSeries.HasSubst.X (S := K) x)) hB
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one] at this
    simp only [T, hX, series_at_variable_const] at this
    exact this
  have F1a := F1 0
  have AutomorphicLevelEquivariance := F1 1
  rw [hC] at F1a AutomorphicLevelEquivariance
  have key := ring_core (MvPowerSeries.X 0 : A2) (MvPowerSeries.X 1) (at1 0 P) (at1 1 P) (at1 0 (dz P))
    (at1 1 (dz P)) (at1 0 (dz (dz P))) (at1 1 (dz (dz P))) (MvPowerSeries.C (g2 / 2)) (MvPowerSeries.C g3)
    (by linear_combination F1a) (F2 0) (by linear_combination AutomorphicLevelEquivariance) (F2 1)
  unfold Lop
  rw [pderiv_zero_zero_weierstrass_difference, pderiv_one_one_weierstrass_difference, pderiv_zero_weierstrass_difference, pderiv_one_weierstrass_difference]
  unfold wpDiff
  linear_combination key
end Formalism.L2.Th1.B.Add0
