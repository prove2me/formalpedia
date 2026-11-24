-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_fLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:22.744643+00:00
-- url     : https://prove2.me/submissions/78bbb4ed-3d7f-4e80-8adb-6374d226cb39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_psubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Map
open Formalism.InvariantFactorPaths.G7 (at1 cob)
variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
namespace Formalism.L2.Th1.B.Map
theorem _root_.solution {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 1) :
    MvPowerSeries.map j (fLog a) = fLog (MvPowerSeries.map j a) := by
  have h' : MvPowerSeries.constantCoeff (a - 1) = 0 := by rw [map_sub, ha, map_one, sub_self]
  unfold Formalism.L2.Th1.B.fLog
  rw [map_psubst j h', map_sub, map_one, PowerSeries.map_log]
end Formalism.L2.Th1.B.Map
