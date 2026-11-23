-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.vc_vz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:02.869713+00:00
-- url     : https://prove2.me/submissions/49d007a8-5bed-4875-92cf-327bdcf737e1

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
theorem _root_.solution (l : Fin r) : (vc l : Var r) ≠ vz := by
  intro h; have := congrArg (fun p : Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this
end Formalism.FourierDecayAlt.P.Mx2
