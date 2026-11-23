-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.pbP_0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:24.725357+00:00
-- url     : https://prove2.me/submissions/c1ced2ef-7219-4277-952d-644c0cf41793

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDerivBar_mul_fn

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
theorem _root_.solution (l : Fin r) (f fb : Fn r) (h1 : euler (vcb l) f = 0) (h2 : euler (vc l) fb = 0) :
    pbP l * fnP f fb = fnP f fb * pbP l := by rw [partialDerivBar_mul_fn, h1, h2, multiplierPair_zero, add_zero]
end Formalism.FourierDecayAlt.P.Mx2
