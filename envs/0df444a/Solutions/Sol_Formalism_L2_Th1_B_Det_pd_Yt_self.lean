-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.pd_Yt_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:23:04.689946+00:00
-- url     : https://prove2.me/submissions/f913f14d-4a52-4241-92bb-7c10b2e21e96

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Det_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_Det_pd_neg_two
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
    MvPowerSeries.pderiv K j (Yt P j) = dYt P j := by
  simp only [Yt, dYt, map_add, Derivation.leibniz, Derivation.leibniz_pow, pd_neg_two,
    MvPowerSeries.pderiv_X_self, partialDeriv_inVar_self, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring
end Formalism.L2.Th1.B.Det
