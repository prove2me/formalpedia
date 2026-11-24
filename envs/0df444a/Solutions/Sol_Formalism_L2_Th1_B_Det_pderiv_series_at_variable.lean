-- Prove2me | solution 1 for Formalism.L2.Th1.B.Det.pderiv_series_at_variable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:03:48.867599+00:00
-- url     : https://prove2.me/submissions/440d339b-abc4-4d92-8237-340958924daa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_Wp3ApplyEqSqMulSubSqMul
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst


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
theorem _root_.solution (i x : Fin 3) (f : PowerSeries K) :
    pd i (at1 x f : A3) = at1 x (dz f) * pd i (MvPowerSeries.X x : A3) := by
  show MvPowerSeries.pderiv K i (PowerSeries.subst (MvPowerSeries.X x : A3) f) =
    PowerSeries.subst (MvPowerSeries.X x : A3) (PowerSeries.derivative K f) * MvPowerSeries.pderiv K i (MvPowerSeries.X x : A3)
  exact Formalism.G.LogCR.pderiv_psubst (by simp) f i
end Formalism.L2.Th1.B.Det
