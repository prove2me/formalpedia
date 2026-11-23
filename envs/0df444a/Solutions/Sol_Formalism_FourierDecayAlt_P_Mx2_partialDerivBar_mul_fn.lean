-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.partialDerivBar_mul_fn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:05.048726+00:00
-- url     : https://prove2.me/submissions/8cf77f99-79ac-4ea1-9f8c-4901e47f8466

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_der_fn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDerivBar_def

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
theorem _root_.solution (l : Fin r) (f fb : Fn r) : pbP l * fnP f fb = fnP f fb * pbP l + fnP (euler (vcb l) f) (euler (vc l) fb) := by
  rw [partialDerivBar_def, der_fn, one_mul, one_mul]
end Formalism.FourierDecayAlt.P.Mx2
