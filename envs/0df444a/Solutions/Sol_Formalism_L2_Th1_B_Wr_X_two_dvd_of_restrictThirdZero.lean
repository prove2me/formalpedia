-- Prove2me | solution 1 for Formalism.L2.Th1.B.Wr.X_two_dvd_of_restrictThirdZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:14.695023+00:00
-- url     : https://prove2.me/submissions/85f9136c-9ef3-45ec-9f09-39b15390f203

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
import Theorems.Thm_Formalism_L2_Th1_B_Wr_coeff_restrictThirdZero

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
theorem _root_.solution {h : MvPowerSeries (Fin 3) K} (h0 : ev3 h = 0) : X 2 ∣ h := by
  rw [X_dvd_iff]
  intro m hm
  rw [← coeff_restrictThirdZero h m hm, h0]
  simp
end Formalism.L2.Th1.B.Wr
