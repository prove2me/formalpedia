-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.fLog_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:47:58.896798+00:00
-- url     : https://prove2.me/submissions/3540ef58-3f57-4108-b65a-8df41f081d41

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fLog
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add
import Theorems.Thm_Formalism_L2_Th1_B_fExp_fLog
import Theorems.Thm_Formalism_L2_Th1_B_fLog_fExp


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
theorem _root_.solution {ι : Type} {g h : MvPowerSeries ι K} (hg : MvPowerSeries.constantCoeff g = 1)
    (hh : MvPowerSeries.constantCoeff h = 1) : fLog (g * h) = fLog g + fLog h := by
  have hg0 := Formalism.L2.Th1.B.constantCoeff_fLog hg
  have hh0 := Formalism.L2.Th1.B.constantCoeff_fLog hh
  have hs : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.fLog g + Formalism.L2.Th1.B.fLog h) = 0 := by
    rw [map_add, hg0, hh0, add_zero]
  calc Formalism.L2.Th1.B.fLog (g * h) = Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog g) * Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog h)) := by
        rw [Formalism.L2.Th1.B.fExp_fLog hg, Formalism.L2.Th1.B.fExp_fLog hh]
    _ = Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog g + Formalism.L2.Th1.B.fLog h)) := by rw [Formalism.L2.Th1.B.fExp_add hg0 hh0]
    _ = Formalism.L2.Th1.B.fLog g + Formalism.L2.Th1.B.fLog h := Formalism.L2.Th1.B.fLog_fExp hs
end Formalism.L2.Th1.B.ParO
