-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.X_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:13.970665+00:00
-- url     : https://prove2.me/submissions/786dac19-c104-4907-bdf8-7ceea4d213ac

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
    (MvPowerSeries.X j - MvPowerSeries.X k : A3) ≠ 0 :=
  ne_zero_of_pd j (by
    rw [pd, map_sub, MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne hjk.symm, sub_zero])
end Formalism.L2.Th1.B.Fs
