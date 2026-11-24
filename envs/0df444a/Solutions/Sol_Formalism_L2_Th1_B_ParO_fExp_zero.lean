-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.fExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:49:33.031954+00:00
-- url     : https://prove2.me/submissions/40c0afaf-559c-472b-8a4d-8a71526b791b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fExp
import Theorems.Thm_Formalism_L2_Th1_B_fExp_add


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
theorem _root_.solution {ι : Type} : fExp (0 : MvPowerSeries ι K) = 1 := by
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries ι K) = 0 := map_zero _
  have hm : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K) * Formalism.L2.Th1.B.fExp 0 = Formalism.L2.Th1.B.fExp 0 * 1 := by
    rw [mul_one, ← Formalism.L2.Th1.B.fExp_add h0 h0, add_zero]
  have hne : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries ι K) ≠ 0 := by
    intro h
    have h1 := Formalism.L2.Th1.B.constantCoeff_fExp h0
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne hm
end Formalism.L2.Th1.B.ParO
