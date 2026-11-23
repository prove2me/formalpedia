-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.mulOp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:55.801597+00:00
-- url     : https://prove2.me/submissions/a07664fb-008e-4c16-a5c3-31a6736cd348

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
theorem _root_.solution (f g : Fn r) : mulOp f * mulOp g = mulOp (f * g) := by
  ext h : 1; simp [mulOp, mul_assoc]
end Formalism.FourierDecayAlt.P.Mx2
