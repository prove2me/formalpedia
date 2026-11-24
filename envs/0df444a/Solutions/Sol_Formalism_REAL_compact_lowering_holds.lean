-- Prove2me | solution 1 for Formalism.REAL.compact_lowering_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:29:57.862402+00:00
-- url     : https://prove2.me/submissions/1b847cfd-6f72-4a92-a5cc-a8aabf73d2a6

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_compact_span_eq_lowering
import Theorems.Thm_Formalism_REAL_lowering_span_weight_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : KLow := by
  intro V _ _ n ε F μ x h hx
  exact ⟨compact_span_eq_lowering h hx, fun y hy hyw => lowering_span_weight_scalar h hx hy hyw⟩
end Formalism.REAL
