-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.partialDeriv_inVar_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:13:21.573123+00:00
-- url     : https://prove2.me/submissions/2ac8dee6-0881-4cb7-8e86-0338790bac4c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_L2_Th1_B_Det_pderiv_series_at_variable
import Theorems.Thm_Formalism_L2_Th1_B_Add0_pderiv_series_at_variable


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
theorem _root_.solution {i x : Fin 3} (h : x ≠ i) (f : PowerSeries K) : pd i (at1 x f : A3) = 0 := by
  rw [pderiv_series_at_variable, show pd i (MvPowerSeries.X x : A3) = 0 by
    simp [MvPowerSeries.pderiv_X, Pi.single_eq_of_ne h], mul_zero]
end Formalism.L2.Th1.B.Det
