-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.triple_lintegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:01.565871+00:00
-- url     : https://prove2.me/submissions/42bd3f3a-f5e3-4cd7-87b3-68e25141beec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul

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
theorem _root_.solution (x : Fin 3) (f : PowerSeries K) :
    (at1 x f : A3) = PowerSeries.substAlgHom (PowerSeries.HasSubst.X x) f := by
  rw [PowerSeries.coe_substAlgHom]; rfl
end Formalism.L2.Th1.B.Det
