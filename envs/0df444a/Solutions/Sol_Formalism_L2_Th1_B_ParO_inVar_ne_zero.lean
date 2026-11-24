-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.inVar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:21:25.131958+00:00
-- url     : https://prove2.me/submissions/03af4ace-bf3d-4d8c-b939-4c512f0e4fa8

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
theorem _root_.solution {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) (x : Fin 2) :
    at1 x l ≠ 0 := by
  intro h
  have h2 := congrArg (fun φ => MvPowerSeries.coeff (Finsupp.single x 1) φ) h
  simp only [Formalism.InvariantFactorPaths.G7.at1, map_zero, PowerSeries.coeff_subst_single] at h2
  simp [hl1] at h2
end Formalism.L2.Th1.B.ParO
