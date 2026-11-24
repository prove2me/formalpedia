-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_cob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:33:35.979441+00:00
-- url     : https://prove2.me/submissions/bd892b77-4a38-4544-bfe5-c5490cc8d7e3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_inVar

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
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    MvPowerSeries.map j (cob F f) = cob (MvPowerSeries.map j F) (PowerSeries.map j f) := by
  unfold Formalism.InvariantFactorPaths.G7.cob
  rw [map_sub, map_sub, map_psubst j hF, map_inVar, map_inVar]
end Formalism.L2.Th1.B.Map
