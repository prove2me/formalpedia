-- Prove2me | solution 1 for Formalism.FG.inverse_integral_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:43.233489+00:00
-- url     : https://prove2.me/submissions/e476e014-8992-492c-bb72-9151275dbdd9

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Theorems.Thm_Formalism_FG_InvIntVAux_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
namespace Formalism.FG
theorem _root_.solution : Formalism.FG.InvIntegralV.{u, v, w} := by
  intro K _ _ ι _ _ τ _ C f hf hsub hP hlowC h hh0 hCh
  exact Formalism.FG.InvIntVAux.main ι τ C f hf hsub hP hlowC h hh0 hCh
end Formalism.FG
