-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_wOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:23:31.106114+00:00
-- url     : https://prove2.me/submissions/4d7ab56b-8458-4aeb-8a81-92a3cc584166

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_inv__a3b389717e67

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
theorem _root_.solution (e1 : K) (P : PowerSeries K) :
    PowerSeries.map j (wOf e1 P) = wOf (j e1) (PowerSeries.map j P) := by
  have hc : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) ≠ 0 := by
    simp
  unfold Formalism.L2.Th1.B.wOf
  rw [map_mul, map_inv' j hc]
  simp only [map_pow, map_sub, map_add, map_one, map_mul, PowerSeries.map_X, PowerSeries.map_C]
end Formalism.L2.Th1.B.Map
