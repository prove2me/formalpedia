-- Prove2me | solution 1 for Formalism.L2.Th1.B.constantCoeff_fExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:30.286423+00:00
-- url     : https://prove2.me/submissions/fa91817d-ebe6-4a21-97be-dd110c4cfe7b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_exp_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
variable {K : Type} [Field K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (fExp f) = 1 :=
  constantCoeff_exp_subst hf
end Formalism.L2.Th1.B
