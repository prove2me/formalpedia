-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add1.partialDeriv_inVar_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:23.658634+00:00
-- url     : https://prove2.me/submissions/aa82f620-6b75-4b72-9190-71eb47baaa81

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Add1
theorem _root_.solution (x : Fin 2) (f : PowerSeries K) : pd x (at1 x f) = at1 x (dz f) := by
  show MvPowerSeries.pderiv K x (PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) f) =
    PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) (PowerSeries.derivative K f)
  rw [Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X x) f x,
    MvPowerSeries.pderiv_X_self, mul_one]
end Formalism.L2.Th1.B.Add1
