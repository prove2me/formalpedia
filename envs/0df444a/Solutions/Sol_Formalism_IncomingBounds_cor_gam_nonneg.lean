-- Prove2me | solution 1 for Formalism.IncomingBounds.cor_gam_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:58.401448+00:00
-- url     : https://prove2.me/submissions/f338e416-6418-401d-82e3-1900b24a0590

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution {l : ℕ} (hl : 3 ≤ l) : 0 ≤ gam l := by
  unfold gam
  have : (3:ℝ) ≤ l := by exact_mod_cast hl
  apply div_nonneg <;> nlinarith
end Formalism.IncomingBounds
