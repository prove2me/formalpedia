-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.X_mul_dYt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:02:57.926565+00:00
-- url     : https://prove2.me/submissions/45b0cccd-a5d3-4f75-97f0-4afff0e818cf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_wpReduced


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
    MvPowerSeries.X j * dYt P j =
      6 * Xt P j ^ 2 - MvPowerSeries.C (g2 / 2) * MvPowerSeries.X j ^ 4 + 3 * Yt P j := by
  have h' := congrArg (PowerSeries.substAlgHom (R := K) (PowerSeries.HasSubst.X (S := K) (τ := Fin 3) j)) (wpReduced K g2 g3 P hP).2
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X (R := K) (PowerSeries.HasSubst.X (S := K) j), PowerSeries.subst_C] at h'
  simp only [dYt, Xt, Yt, Formalism.InvariantFactorPaths.G7.at1]
  linear_combination MvPowerSeries.X j ^ 2 * h'
end Formalism.L2.Th1.B.Det
