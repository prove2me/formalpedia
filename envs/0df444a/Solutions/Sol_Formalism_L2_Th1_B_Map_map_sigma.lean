-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:49:24.862318+00:00
-- url     : https://prove2.me/submissions/705f7366-e3b7-400c-a5a1-1bbf14ae83a5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_fExp__32d85cf1f169
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_sigS
import Theorems.Thm_Formalism_L2_Th1_B_Map_cc_sigS

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
theorem _root_.solution (P : PowerSeries K) :
    PowerSeries.map j (sigma P) = sigma (PowerSeries.map j P) := by
  unfold Formalism.L2.Th1.B.sigma
  rw [map_mul, PowerSeries.map_X, map_fExp' j (cc_sigS P),
    map_sigS]
end Formalism.L2.Th1.B.Map
