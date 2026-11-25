-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.supremum_A_is_majorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:54:12.656167+00:00
-- url     : https://prove2.me/submissions/91932209-d301-444f-b714-581a8cf81c85

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_sup_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : SupAIsCore := by
  intro ι _ G de de' T T' l w hg hk
  constructor
  · exact sup_core G de de' T T' w hg hk _
  · exact sup_core G de de' T T' w hg hk _
end Formalism.FourierDecayAlt.P
