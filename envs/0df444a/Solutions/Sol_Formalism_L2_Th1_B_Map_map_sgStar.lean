-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_sgStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:59.874975+00:00
-- url     : https://prove2.me/submissions/73110f49-a270-4e8d-bb74-7c2c29dc28a7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_fExp__32d85cf1f169
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_sigma

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
theorem _root_.solution (s2 : K) (P : PowerSeries K) :
    PowerSeries.map j (sgStar s2 P) = sgStar (j s2) (PowerSeries.map j P) := by
  have hc : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) = 0 := by
    simp
  unfold Formalism.L2.Th1.B.sgStar
  rw [map_mul, map_sigma, map_fExp' j hc, map_neg, map_mul, PowerSeries.map_C,
    map_pow, PowerSeries.map_X, map_div₀, map_ofNat]
end Formalism.L2.Th1.B.Map
