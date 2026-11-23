-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.multiplierPair_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:20.184805+00:00
-- url     : https://prove2.me/submissions/bccfca01-11ca-435a-8905-c1ed2649eeb7

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations

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
theorem _root_.solution : (fnP 0 0 : Pr r) = 0 := by
  have h0 : mulOp (0 : Fn r) = 0 := by ext h : 1; simp [mulOp]
  refine Prod.ext h0 ?_
  show MulOpposite.op (mulOp (0 : Fn r)) = 0
  rw [h0]; rfl
end Formalism.FourierDecayAlt.P.Mx2
