-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.X_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:12.573852+00:00
-- url     : https://prove2.me/submissions/86fb9053-5db4-4c27-a49f-6d29705b89a9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_ne_zero_of_pd

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
    (MvPowerSeries.X j + MvPowerSeries.X k : A3) ≠ 0 :=
  ne_zero_of_pd j (by
    rw [pd, map_add, MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne hjk.symm, add_zero])
end Formalism.L2.Th1.B.Fs
