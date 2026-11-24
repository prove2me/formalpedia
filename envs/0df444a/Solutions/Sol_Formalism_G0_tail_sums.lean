-- Prove2me | solution 1 for Formalism.G0.tail_sums
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:15.618403+00:00
-- url     : https://prove2.me/submissions/4c127399-cf04-4877-8e99-bc4548a954be

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums
import Theorems.Thm_Formalism_G0_TailSumsP_clause1
import Theorems.Thm_Formalism_G0_TailSumsP_clause2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution : TailSums := by
  intro K steps what₂ hp
  refine ⟨TailSumsP.clause1 steps what₂ hp, ?_⟩
  intro i j u X hij hj hX
  exact TailSumsP.clause2 steps what₂ hp i u X hX j hij hj
end Formalism.G0
