-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.multiplierPair_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:20.931998+00:00
-- url     : https://prove2.me/submissions/f50712f5-a4e3-469d-b35b-67478aaf5e61

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_mul

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
theorem _root_.solution (f fb g gb : Fn r) : fnP f fb * fnP g gb = fnP g gb * fnP f fb := by
  rw [multiplierPair_mul, multiplierPair_mul, mul_comm f, mul_comm fb]
end Formalism.FourierDecayAlt.P.Mx2
