-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.inVar_sub_inVar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:21:25.874088+00:00
-- url     : https://prove2.me/submissions/9d268059-4101-4088-9efb-9750483929be

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
theorem _root_.solution {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) :
    at1 (0 : Fin 2) l - at1 1 l ≠ 0 := by
  intro h
  have h2 := congrArg (fun φ => MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) φ) h
  simp only [Formalism.InvariantFactorPaths.G7.at1, map_sub, map_zero, PowerSeries.coeff_subst_single] at h2
  simp [hl1] at h2
end Formalism.L2.Th1.B.ParO
