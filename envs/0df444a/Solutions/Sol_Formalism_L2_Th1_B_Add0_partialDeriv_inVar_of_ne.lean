-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.partialDeriv_inVar_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:26.856654+00:00
-- url     : https://prove2.me/submissions/5ccc55ef-b12a-4d5a-8a49-211c44438f13

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]
local notation "A2" => MvPowerSeries (Fin 2) K
namespace Formalism.L2.Th1.B.Add0
theorem _root_.solution {i x : Fin 2} (h : x ≠ i) (f : PowerSeries K) : pd i (at1 x f : A2) = 0 := by
  rw [pderiv_series_at_variable, show pd i (MvPowerSeries.X x : A2) = 0 from MvPowerSeries.pderiv_X_of_ne h, mul_zero]
end Formalism.L2.Th1.B.Add0
