-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.curve_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:00.920717+00:00
-- url     : https://prove2.me/submissions/59d2926c-709d-4820-94f7-547bfe58e33c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Det
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K
namespace Formalism.L2.Th1.B.Det
theorem _root_.solution {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) (j : Fin 3) :
    Yt P j ^ 2 = 4 * Xt P j ^ 3 - 2 * MvPowerSeries.C (g2 / 2) * MvPowerSeries.X j ^ 4 * Xt P j -
      MvPowerSeries.C g3 * MvPowerSeries.X j ^ 6 := by
  have h' := congrArg (PowerSeries.substAlgHom (R := K) (PowerSeries.HasSubst.X (S := K) (τ := Fin 3) j)) hP.2.2
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X (R := K) (PowerSeries.HasSubst.X (S := K) j), PowerSeries.subst_C] at h'
  have hc : (MvPowerSeries.C g2 : A3) = 2 * MvPowerSeries.C (g2 / 2) := by
    conv_lhs => rw [show g2 = 2 * (g2 / 2) by ring]
    rw [map_mul, map_ofNat]
  simp only [Xt, Yt, Formalism.InvariantFactorPaths.G7.at1]
  linear_combination h' - (MvPowerSeries.X j ^ 4 * (1 + MvPowerSeries.X j ^ 2 * PowerSeries.subst (MvPowerSeries.X j : A3) P)) * hc
end Formalism.L2.Th1.B.Det
