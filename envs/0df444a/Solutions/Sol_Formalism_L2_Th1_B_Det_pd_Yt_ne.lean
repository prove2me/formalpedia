-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.pd_Yt_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:23:03.143177+00:00
-- url     : https://prove2.me/submissions/297f2f84-d9a0-4d4d-9393-92652a3960a4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Det_partialDeriv_inVar_of_ne
import Theorems.Thm_Formalism_L2_Th1_B_Det_pd_neg_two
import Theorems.Thm_Formalism_L2_Th1_B_Add0_partialDeriv_inVar_of_ne
import Theorems.Thm_Formalism_L2_Th1_B_Add1_partialDeriv_inVar_of_ne


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
theorem _root_.solution (P : PowerSeries K) {i j : Fin 3} (h : j ≠ i) :
    MvPowerSeries.pderiv K i (Yt P j) = 0 := by
  simp [Yt, Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h,
    partialDeriv_inVar_of_ne h, pd_neg_two]
end Formalism.L2.Th1.B.Det
