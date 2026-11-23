-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nab_cf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:59.755865+00:00
-- url     : https://prove2.me/submissions/ac889b0d-971f-42ff-a326-fccc61a972c8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabE_fn
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
theorem _root_.solution (a TT : ℝ) (f fb : Fn r) (h1 : euler vz f = 0) (h2 : euler vzb fb = 0) :
    nabE a TT * fnP f fb = fnP f fb * nabE a TT := by
  rw [nabE_fn, h1, h2, mul_zero, mul_zero, multiplierPair_zero, add_zero]
end Formalism.FourierDecayAlt.P.Mx2
