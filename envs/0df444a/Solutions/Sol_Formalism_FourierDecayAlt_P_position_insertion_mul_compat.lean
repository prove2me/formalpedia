-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.position_insertion_mul_compat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:10.640911+00:00
-- url     : https://prove2.me/submissions/a1cbe38e-3c06-4222-a79b-178ad54d6a62

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.InsMul := by
  intro K A S _ _ _ _ _ _ _ _ a M N hM
  exact Wd1.ins_mul a M N hM
end Formalism.FourierDecayAlt.P
