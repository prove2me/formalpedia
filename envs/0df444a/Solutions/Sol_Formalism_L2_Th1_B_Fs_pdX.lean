-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.pdX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:17.171646+00:00
-- url     : https://prove2.me/submissions/d636a4df-3486-4df8-8fce-ec566e14e3a2

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
theorem _root_.solution (i j : Fin 3) :
    MvPowerSeries.pderiv K i (MvPowerSeries.X j : A3) = if j = i then 1 else 0 := by
  split_ifs with h
  · rw [h, MvPowerSeries.pderiv_X_self]
  · rw [MvPowerSeries.pderiv_X_of_ne h]
end Formalism.L2.Th1.B.Fs
