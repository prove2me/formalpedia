-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.det_three_points_eq_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:03:13.926518+00:00
-- url     : https://prove2.me/submissions/0c931679-0d47-452b-b113-b2ac7de62e3e

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
theorem _root_.solution (P : PowerSeries K) :
    det3 P = MvPowerSeries.X 0 ^ 3 * (MvPowerSeries.X 1 * Xt P 1 * Yt P 2 -
        Yt P 1 * (MvPowerSeries.X 2 * Xt P 2)) -
      MvPowerSeries.X 0 * Xt P 0 * (MvPowerSeries.X 1 ^ 3 * Yt P 2 -
        Yt P 1 * MvPowerSeries.X 2 ^ 3) +
      Yt P 0 * (MvPowerSeries.X 1 ^ 3 * (MvPowerSeries.X 2 * Xt P 2) -
        MvPowerSeries.X 1 * Xt P 1 * MvPowerSeries.X 2 ^ 3) := by
  simp [det3, Matrix.det_fin_three, Xt, Yt]
  ring
end Formalism.L2.Th1.B.Det
