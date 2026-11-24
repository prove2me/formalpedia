-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.psubst_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:21:14.441483+00:00
-- url     : https://prove2.me/submissions/edae5286-6577-44a9-a0d9-17989e5593ac

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParO
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.ParO
theorem _root_.solution (l : PowerSeries K) (c : K) :
    PowerSeries.subst l (PowerSeries.C c) = PowerSeries.C c :=
  PowerSeries.subst_C c
end Formalism.L2.Th1.B.ParO
