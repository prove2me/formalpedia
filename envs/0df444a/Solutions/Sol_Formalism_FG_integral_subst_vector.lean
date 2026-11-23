-- Prove2me | solution 1 for Formalism.FG.integral_subst_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:40.062832+00:00
-- url     : https://prove2.me/submissions/e753e427-9532-4e17-a1a6-a3c5a3e4cbbd

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV

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
theorem _root_.solution : Formalism.FG.IntegralSubstV.{u, v, w} :=
  fun _ _ _ _ _ _ g a hg ha0 ha => Formalism.FG.IntegralSubstitution.integralSubstV g a hg ha0 ha
end Formalism.FG
