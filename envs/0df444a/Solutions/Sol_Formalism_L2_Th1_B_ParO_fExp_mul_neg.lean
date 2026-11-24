-- Prove2me | solution 1 for Formalism.L2.Th1.B.ParO.fExp_mul_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:00.660649+00:00
-- url     : https://prove2.me/submissions/49a0668b-a7bc-4101-abf3-d050d865591a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InVarAddInVarNeZero
import Theorems.Thm_Formalism_L2_Th1_B_ParO_fExp_zero
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
theorem _root_.solution {ι : Type} {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    fExp f * fExp (-f) = 1 := by
  have hnf : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf, neg_zero]
  rw [← Formalism.L2.Th1.B.fExp_add hf hnf, add_neg_cancel, fExp_zero]
end Formalism.L2.Th1.B.ParO
