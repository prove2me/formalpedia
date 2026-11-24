-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.pderiv_one_det_three_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:52.516362+00:00
-- url     : https://prove2.me/submissions/fd13d708-539e-44d1-9d32-3743ca2d9ee9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Det_pd_Xt_self
import Theorems.Thm_Formalism_L2_Th1_B_Det_pd_Xt_ne
import Theorems.Thm_Formalism_L2_Th1_B_Det_pd_Yt_self
import Theorems.Thm_Formalism_L2_Th1_B_Det_pd_Yt_ne
import Theorems.Thm_Formalism_L2_Th1_B_Det_det_three_points_eq_expansion

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
theorem _root_.solution (P : PowerSeries K) :
    pd 1 (det3 P) = MvPowerSeries.X 0 ^ 3 * ((Xt P 1 + MvPowerSeries.X 1 * dXt P 1) * Yt P 2 -
        dYt P 1 * (MvPowerSeries.X 2 * Xt P 2)) -
      MvPowerSeries.X 0 * Xt P 0 * (3 * MvPowerSeries.X 1 ^ 2 * Yt P 2 -
        dYt P 1 * MvPowerSeries.X 2 ^ 3) +
      Yt P 0 * (3 * MvPowerSeries.X 1 ^ 2 * (MvPowerSeries.X 2 * Xt P 2) -
        (Xt P 1 + MvPowerSeries.X 1 * dXt P 1) * MvPowerSeries.X 2 ^ 3) := by
  have h0 : (0 : Fin 3) ≠ 1 := by decide
  have h2 : (2 : Fin 3) ≠ 1 := by decide
  rw [det_three_points_eq_expansion]
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X_self,
    MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h2, pd_Xt_self, pd_Xt_ne P h0,
    pd_Xt_ne P h2, pd_Yt_self, pd_Yt_ne P h0, pd_Yt_ne P h2, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring
end Formalism.L2.Th1.B.Det
