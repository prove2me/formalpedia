-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.sq_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:13.825215+00:00
-- url     : https://prove2.me/submissions/1cf3fb23-e3ec-4317-8f68-b72378de71b3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_X_sub_ne_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_X_add_ne_zero

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
theorem _root_.solution {j k : Fin 3} (hjk : j ≠ k) :
    (MvPowerSeries.X j ^ 2 - MvPowerSeries.X k ^ 2 : A3) ≠ 0 := by
  rw [sq_sub_sq]
  exact mul_ne_zero (X_add_ne_zero hjk) (X_sub_ne_zero hjk)
end Formalism.L2.Th1.B.Fs
