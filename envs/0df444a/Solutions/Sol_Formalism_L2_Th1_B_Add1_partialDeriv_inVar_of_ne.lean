-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add1.partialDeriv_inVar_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:22.1951+00:00
-- url     : https://prove2.me/submissions/fb58b283-c099-48b3-84f9-bb0c8b2a82a4

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
theorem _root_.solution {x y : Fin 2} (h : y ≠ x) (f : PowerSeries K) : pd x (at1 y f) = 0 := by
  show MvPowerSeries.pderiv K x (PowerSeries.subst (MvPowerSeries.X y : MvPowerSeries (Fin 2) K) f) = 0
  rw [Formalism.G.LogCR.pderiv_psubst (MvPowerSeries.constantCoeff_X y) f x,
    MvPowerSeries.pderiv_X_of_ne h, mul_zero]
end Formalism.L2.Th1.B.Add1
