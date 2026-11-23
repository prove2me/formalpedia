-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.euler_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:51.720616+00:00
-- url     : https://prove2.me/submissions/0fa8f3d6-fa92-40e7-8732-fa5fe7e89bc3

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerCoord

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
theorem _root_.solution (v : Var r) : euler v (1 : Fn r) = 0 := by
  have := (eulerCoord r v v 1).2
  simpa using this
end Formalism.FourierDecayAlt.P.Mx2
