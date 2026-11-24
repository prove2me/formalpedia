-- Prove2me | solution 1 for Formalism.IncomingBounds.cor_gam_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:11.883935+00:00
-- url     : https://prove2.me/submissions/65552c32-ad5c-4e0c-bd77-78a939ceee3f

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
theorem _root_.solution {l : ℕ} (hl : 3 ≤ l) : gam l ≤ 9 / (8 * l) := by
  unfold gam
  have h3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith
end Formalism.IncomingBounds
