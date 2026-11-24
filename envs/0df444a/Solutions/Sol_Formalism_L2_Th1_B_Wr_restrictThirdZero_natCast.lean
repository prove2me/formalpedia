-- Prove2me | solution 1 for Formalism.L2.Th1.B.Wr.restrictThirdZero_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:13:11.692766+00:00
-- url     : https://prove2.me/submissions/af4ec238-bad5-47a3-a1ea-8584e72e2fd1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
import Theorems.Thm_Formalism_L2_Th1_B_Wr_restrictThirdZero_eq_rescale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Wr
theorem _root_.solution (k : ℕ) : ev3 (k : MvPowerSeries (Fin 3) K) = k := by
  simp only [restrictThirdZero_eq_rescale, map_natCast]
end Formalism.L2.Th1.B.Wr
