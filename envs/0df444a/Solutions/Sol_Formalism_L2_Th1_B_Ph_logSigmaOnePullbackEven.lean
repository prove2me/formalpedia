-- Prove2me | solution 1 for Formalism.L2.Th1.B.Ph.logSigmaOnePullbackEven
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:30.985824+00:00
-- url     : https://prove2.me/submissions/479e029c-3026-4d2a-9f62-cdb27281d51f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Theorems.Thm_Formalism_L2_Th1_B_Ph_phE_inv

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
theorem _root_.solution : PhEEven := by
  intro K _ _ _ s2 e1 kap w l i hw hl hinv
  obtain ⟨hi, _, hli⟩ := hinv
  exact phE_inv s2 e1 kap hw hl hi hli
end Formalism.L2.Th1.B.Ph
