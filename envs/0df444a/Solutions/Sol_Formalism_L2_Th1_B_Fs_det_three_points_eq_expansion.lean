-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.det_three_points_eq_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:49.12023+00:00
-- url     : https://prove2.me/submissions/52011ef1-02dc-4777-9311-a3dd804229bc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt

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
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K
namespace Formalism.L2.Th1.B.Fs
theorem _root_.solution (P : PowerSeries K) : det3 P =
    MvPowerSeries.X 0 ^ 3 * (MvPowerSeries.X 1 * (1 + MvPowerSeries.X 1 ^ 2 * at1 1 P)) *
        (-2 + MvPowerSeries.X 2 ^ 3 * at1 2 (dz P)) -
      MvPowerSeries.X 0 ^ 3 * (-2 + MvPowerSeries.X 1 ^ 3 * at1 1 (dz P)) *
        (MvPowerSeries.X 2 * (1 + MvPowerSeries.X 2 ^ 2 * at1 2 P)) -
      MvPowerSeries.X 0 * (1 + MvPowerSeries.X 0 ^ 2 * at1 0 P) * MvPowerSeries.X 1 ^ 3 *
        (-2 + MvPowerSeries.X 2 ^ 3 * at1 2 (dz P)) +
      MvPowerSeries.X 0 * (1 + MvPowerSeries.X 0 ^ 2 * at1 0 P) *
        (-2 + MvPowerSeries.X 1 ^ 3 * at1 1 (dz P)) * MvPowerSeries.X 2 ^ 3 +
      (-2 + MvPowerSeries.X 0 ^ 3 * at1 0 (dz P)) * MvPowerSeries.X 1 ^ 3 *
        (MvPowerSeries.X 2 * (1 + MvPowerSeries.X 2 ^ 2 * at1 2 P)) -
      (-2 + MvPowerSeries.X 0 ^ 3 * at1 0 (dz P)) *
        (MvPowerSeries.X 1 * (1 + MvPowerSeries.X 1 ^ 2 * at1 1 P)) * MvPowerSeries.X 2 ^ 3 := by
  rw [det3, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
end Formalism.L2.Th1.B.Fs
