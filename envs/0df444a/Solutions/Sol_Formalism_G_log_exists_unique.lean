-- Prove2me | solution 1 for Formalism.G.log_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:49.680798+00:00
-- url     : https://prove2.me/submissions/353126dd-5834-46e7-8369-6001f1a08c4d

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_log_unique
import Theorems.Thm_Formalism_G_LogP_logF_isLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace Formalism.G
theorem _root_.solution : Formalism.G.LogExistsUnique := by
  intro R _ _ F
  exact ⟨Formalism.G.LogP.logF F, Formalism.G.LogP.logF_isLog F,
    fun g hg => Formalism.G.LogP.log_unique F hg (Formalism.G.LogP.logF_isLog F)⟩
end Formalism.G
