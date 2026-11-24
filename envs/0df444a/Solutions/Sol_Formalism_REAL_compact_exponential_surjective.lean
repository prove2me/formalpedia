-- Prove2me | solution 1 for Formalism.REAL.compact_exponential_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:41:12.41084+00:00
-- url     : https://prove2.me/submissions/6f4000f3-c69f-491a-b488-a0feb2361d52

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactExponentialSurjective
import Theorems.Thm_Formalism_REAL_compact_exists_log_bounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : KExp := fun _ ε k hk => compact_exists_log_bounded ε k hk
end Formalism.REAL
