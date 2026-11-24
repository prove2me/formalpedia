-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.pd_Xt_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:23:21.634712+00:00
-- url     : https://prove2.me/submissions/9b3a3808-964b-46e7-80cc-d2158acd5e87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Det_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_Add0_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_Add1_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_partialDeriv_inVar_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Det
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K
namespace Formalism.L2.Th1.B.Det
theorem _root_.solution (P : PowerSeries K) (j : Fin 3) :
    MvPowerSeries.pderiv K j (Xt P j) = dXt P j := by
  simp only [Xt, dXt, map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_one_eq_zero,
    MvPowerSeries.pderiv_X_self, partialDeriv_inVar_self, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring
end Formalism.L2.Th1.B.Det
