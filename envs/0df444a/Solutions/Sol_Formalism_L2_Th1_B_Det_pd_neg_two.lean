-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.pd_neg_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:03:06.606862+00:00
-- url     : https://prove2.me/submissions/e6e5e446-5fe3-4d65-abd3-d532c1b1fe30

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
theorem _root_.solution (i : Fin 3) : MvPowerSeries.pderiv K i (-2 : A3) = 0 := by
  have h2 : MvPowerSeries.pderiv K i (2 : A3) = 0 := by
    simpa using (MvPowerSeries.pderiv K i).map_natCast 2
  rw [map_neg, h2, neg_zero]
end Formalism.L2.Th1.B.Det
