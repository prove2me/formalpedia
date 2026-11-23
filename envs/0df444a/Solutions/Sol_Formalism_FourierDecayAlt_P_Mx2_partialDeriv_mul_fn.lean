-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.partialDeriv_mul_fn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:09.442116+00:00
-- url     : https://prove2.me/submissions/cd5b81b8-9a6f-4c07-8789-1a22a3652053

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_der_fn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_partialDeriv_def

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
theorem _root_.solution (l : Fin r) (f fb : Fn r) : pP l * fnP f fb = fnP f fb * pP l + fnP (euler (vc l) f) (euler (vcb l) fb) := by
  rw [partialDeriv_def, der_fn, one_mul, one_mul]
end Formalism.FourierDecayAlt.P.Mx2
