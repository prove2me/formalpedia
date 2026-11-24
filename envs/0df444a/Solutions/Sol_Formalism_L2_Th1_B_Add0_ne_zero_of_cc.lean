-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.ne_zero_of_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:20:29.482857+00:00
-- url     : https://prove2.me/submissions/5950ed26-83a6-4e23-906f-e0401fe060b5

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
theorem _root_.solution {N : A2} (h : MvPowerSeries.constantCoeff N = 1) : N ≠ 0 := by
  intro h0
  rw [h0, map_zero] at h
  exact zero_ne_one h
end Formalism.L2.Th1.B.Add0
