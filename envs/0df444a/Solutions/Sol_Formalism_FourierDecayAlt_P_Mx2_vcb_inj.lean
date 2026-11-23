-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.vcb_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:44.113501+00:00
-- url     : https://prove2.me/submissions/280490fa-917f-4cd2-86f8-5065e06e9aee

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
theorem _root_.solution (l m : Fin r) : (vcb l : Var r) = vcb m ↔ l = m := by
  constructor
  · intro h; have := congrArg (fun p : Var r => (ofLex p).1) h; simpa [vcb] using this
  · rintro rfl; rfl
end Formalism.FourierDecayAlt.P.Mx2
