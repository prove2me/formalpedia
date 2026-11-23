-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.multiplierPair_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:15.90007+00:00
-- url     : https://prove2.me/submissions/0529c93e-d238-4e5d-97ad-d8d0e73141a7

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_mulOp_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution (f fb g gb : Fn r) : fnP f fb + fnP g gb = fnP (f + g) (fb + gb) := by
  refine Prod.ext ?_ ?_
  · exact mulOp_add f g
  · show MulOpposite.op (mulOp fb + mulOp gb) = MulOpposite.op (mulOp (fb + gb))
    rw [mulOp_add]
end Formalism.FourierDecayAlt.P.Mx2
