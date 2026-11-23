-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.wpDiff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:11.341829+00:00
-- url     : https://prove2.me/submissions/ca47eea4-697a-4fe6-b8e9-98db4d26425d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference

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
theorem _root_.solution (h9 : DqRule) {P : PowerSeries K}
    (hP : ∀ n, Odd n → PowerSeries.coeff n P = 0) :
    wpDiff P = (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) *
      (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P) := by
  have h := h9 K P hP
  unfold wpDiff
  linear_combination (-(MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 : A2)) * h
end Formalism.L2.Th1.B.Add0
