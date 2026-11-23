-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.vc_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:55.980955+00:00
-- url     : https://prove2.me/submissions/4c9a5775-b31b-431c-b107-20a8347bcb66

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
theorem _root_.solution (l m : Fin r) : (vc l : Var r) = vc m ↔ l = m := by
  constructor
  · intro h; have := congrArg (fun p : Var r => (ofLex p).1) h; simpa [vc] using this
  · rintro rfl; rfl
end Formalism.FourierDecayAlt.P.Mx2
