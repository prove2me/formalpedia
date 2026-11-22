-- Prove2me | solution 1 for Formalism.FN.gNorm_bdd_of_conv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:27:53.145576+00:00
-- url     : https://prove2.me/submissions/ab76dec1-e606-44c2-81e2-a6d2fa0466ba

import Definitions.Def_Formalism_SuccessiveMinima_StatementNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FN
open Filter Topology
variable {K : Type*} [NormedField K]
namespace Formalism.FN
theorem _root_.solution (a : ℕ → K) (r : ℝ) (h : ConvOn a r) :
    BddAbove (Set.range fun k : ℕ => ‖a k‖ * r ^ k) := h.bddAbove_range
end Formalism.FN
