-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.realPoints
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:27.498573+00:00
-- url     : https://prove2.me/submissions/d5ddd227-afda-4448-be49-74b74ac9ded3

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution : RealPoints := by
  intro P π Y
  constructor
  · simp [xC, I.xpoly]
  · simp [qC, I.qpoly]
end Formalism.FourierDecayAlt.P.Mx3
