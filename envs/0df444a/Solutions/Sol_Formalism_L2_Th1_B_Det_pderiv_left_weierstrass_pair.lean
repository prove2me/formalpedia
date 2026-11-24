-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.pderiv_left_weierstrass_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:51.647636+00:00
-- url     : https://prove2.me/submissions/42274ce2-481e-4291-855c-58696c128fea

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Det_pd_Xt_self
import Theorems.Thm_Formalism_L2_Th1_B_Det_pd_Xt_ne
import Theorems.Thm_Formalism_L2_Th1_B_Det_wp3_apply_eq_sq_mul_sub_sq_mul

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
theorem _root_.solution (P : PowerSeries K) {j k : Fin 3} (h : k ≠ j) :
    pd j (wp3 P j k) = 2 * MvPowerSeries.X j * Xt P k - MvPowerSeries.X k ^ 2 * dXt P j := by
  rw [wp3_apply_eq_sq_mul_sub_sq_mul]
  simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X_self,
    MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h, pd_Xt_self, pd_Xt_ne P h, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring
end Formalism.L2.Th1.B.Det
