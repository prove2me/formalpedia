-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.multiplierPair_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:11.118811+00:00
-- url     : https://prove2.me/submissions/295dc457-d7f0-4bb9-902a-72a93a35c051

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
theorem _root_.solution : (fnP 1 1 : Pr r) = 1 := by
  have : mulOp (1 : Fn r) = 1 := by ext h : 1; simp [mulOp]
  refine Prod.ext ?_ ?_
  · exact this
  · show MulOpposite.op (mulOp (1 : Fn r)) = 1
    rw [this]; rfl
end Formalism.FourierDecayAlt.P.Mx2
