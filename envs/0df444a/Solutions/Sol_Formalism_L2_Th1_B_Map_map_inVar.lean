-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_inVar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:23.633109+00:00
-- url     : https://prove2.me/submissions/81db9003-9ae4-4a5d-b6e2-8fdd9e87c3cc

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
theorem _root_.solution {ι : Type} (x : ι) (f : PowerSeries K) :
    MvPowerSeries.map j (at1 x f) = at1 x (PowerSeries.map j f) := by
  unfold Formalism.InvariantFactorPaths.G7.at1
  rw [map_psubst j (MvPowerSeries.constantCoeff_X x), MvPowerSeries.map_X]
end Formalism.L2.Th1.B.Map
