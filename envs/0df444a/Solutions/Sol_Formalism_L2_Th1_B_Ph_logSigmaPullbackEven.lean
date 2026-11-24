-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.logSigmaPullbackEven
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:05:55.162305+00:00
-- url     : https://prove2.me/submissions/4fc2a825-3509-4489-8b38-a9c48c728065

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Ph_fExp_phO_inv_sub
import Theorems.Thm_Formalism_L2_Th1_B_Ph_integral_neg_lU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Ph
open PowerSeries
namespace Formalism.L2.Th1.B.Ph
theorem _root_.solution : PhOEven := by
  intro K _ _ _ s2 P l i hP hl hl1 hinv
  obtain ⟨hi, hiI, hli⟩ := hinv
  refine ⟨?_, ?_⟩
  · show constantCoeff (subst i (phO s2 P l) - phO s2 P l) = 0
    rw [map_sub, constantCoeff_psubst hi, sub_self]
  · show Formalism.DworkPowerSeriesWeights.Integral (fExp (subst i (phO s2 P l) - phO s2 P l))
    rw [fExp_phO_inv_sub s2 hP hl hl1 hi hli]
    exact integral_neg_lU hiI
end Formalism.L2.Th1.B.Ph
