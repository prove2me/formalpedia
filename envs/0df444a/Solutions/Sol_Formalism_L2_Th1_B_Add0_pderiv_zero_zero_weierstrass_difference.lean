-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.pderiv_zero_zero_weierstrass_difference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:07.891689+00:00
-- url     : https://prove2.me/submissions/b39831e0-d191-4757-a69f-97127a3a7b2f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_Add0_partialDeriv_inVar_of_ne
import Theorems.Thm_Formalism_L2_Th1_B_Add0_pd_two
import Theorems.Thm_Formalism_L2_Th1_B_Add0_pderiv_zero_weierstrass_difference

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
theorem _root_.solution (P : PowerSeries K) : pd 0 (pd 0 (wpDiff P)) =
    2 + 2 * MvPowerSeries.X 1 ^ 2 * (at1 1 P - at1 0 P) -
      4 * MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 2 * at1 0 (dz P) -
      MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * at1 0 (dz (dz P)) := by
  rw [pderiv_zero_weierstrass_difference]
  have s0 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 0 (at1 0 f : A2) = at1 0 (dz f) :=
    fun f => partialDeriv_inVar_self 0 f
  have s1 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 1 (at1 1 f : A2) = at1 1 (dz f) :=
    fun f => partialDeriv_inVar_self 1 f
  have n01 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 0 (at1 1 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have n10 : ∀ f : PowerSeries K, MvPowerSeries.pderiv K 1 (at1 0 f : A2) = 0 :=
    fun f => partialDeriv_inVar_of_ne (by decide) f
  have t0 : MvPowerSeries.pderiv K 0 (2 : A2) = 0 := pd_two 0
  have t1 : MvPowerSeries.pderiv K 1 (2 : A2) = 0 := pd_two 1
  simp only [pd, map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne (i := (0 : Fin 2)) (j := 1) (by decide),
    MvPowerSeries.pderiv_X_of_ne (i := (1 : Fin 2)) (j := 0) (by decide), s0, s1, n01, n10, t0, t1,
    map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero, Nat.cast_ofNat, pow_one, pow_zero,
    Nat.add_one_sub_one]
  ring
end Formalism.L2.Th1.B.Add0
