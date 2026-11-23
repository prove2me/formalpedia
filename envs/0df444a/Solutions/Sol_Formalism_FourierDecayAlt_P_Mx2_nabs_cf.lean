-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nabs_cf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:00.375225+00:00
-- url     : https://prove2.me/submissions/cb0e80fb-f3fa-4707-aa6a-86ac3fc0940c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabsE_fn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_zero

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
theorem _root_.solution (a TT : ℝ) (f fb : Fn r) (h1 : euler vzb f = 0) (h2 : euler vz fb = 0) :
    nabsE a TT * fnP f fb = fnP f fb * nabsE a TT := by
  rw [nabsE_fn, h1, h2, mul_zero, mul_zero, multiplierPair_zero, sub_zero]
end Formalism.FourierDecayAlt.P.Mx2
