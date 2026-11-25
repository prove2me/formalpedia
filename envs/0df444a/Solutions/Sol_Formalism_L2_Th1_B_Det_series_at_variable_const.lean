-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.series_at_variable_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:21:22.551088+00:00
-- url     : https://prove2.me/submissions/f53040c3-a984-451e-91f8-17bd0250d478

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
theorem _root_.solution (x : Fin 3) (c : K) : (at1 x (PowerSeries.C c) : A3) = MvPowerSeries.C c := by
  show PowerSeries.subst (MvPowerSeries.X x : A3) (PowerSeries.C c) = MvPowerSeries.C c
  exact PowerSeries.subst_C c
end Formalism.L2.Th1.B.Det
