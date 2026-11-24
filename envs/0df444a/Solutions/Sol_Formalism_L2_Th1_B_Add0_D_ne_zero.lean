-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.D_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:20:22.904803+00:00
-- url     : https://prove2.me/submissions/4821e703-b10d-489c-ae98-19dbdc8dd4c4

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
theorem _root_.solution : (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2 : A2) ≠ 0 := by
  intro h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 2)) h
  have hne : (Finsupp.single (0 : Fin 2) 2) ≠ Finsupp.single 1 2 := by
    intro h'
    have := (Finsupp.single_left_inj two_ne_zero).1 h'
    exact absurd this (by decide)
  simp [MvPowerSeries.coeff_X_pow, hne] at this
end Formalism.L2.Th1.B.Add0
