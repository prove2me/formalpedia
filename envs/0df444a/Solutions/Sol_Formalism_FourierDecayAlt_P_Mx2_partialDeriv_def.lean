-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.partialDeriv_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:32.691837+00:00
-- url     : https://prove2.me/submissions/1896bab5-5e90-41c8-9198-5a1a2b8eeb33

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
theorem _root_.solution (l : Fin r) : (pP l : Pr r) = mk (mulOp 1 * euler (vc l)) (-(mulOp 1 * euler (vcb l))) := by
  have : mulOp (1 : Fn r) = 1 := by ext h : 1; simp [mulOp]
  rw [this, one_mul, one_mul]; rfl
end Formalism.FourierDecayAlt.P.Mx2
