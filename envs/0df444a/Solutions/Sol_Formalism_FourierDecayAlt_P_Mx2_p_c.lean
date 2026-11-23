-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.p_c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:00.790526+00:00
-- url     : https://prove2.me/submissions/fdc31c92-2fd4-4bda-bbcf-998fa44f90a8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerCoord
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
theorem _root_.solution (l : Fin r) : pP l * cP l = cP l * pP l + cP l := by
  rw [partialDeriv_def, cP, der_fn, (eulerCoord r _ _ 0).1, (eulerCoord r _ _ 0).1, if_pos rfl, if_pos rfl, one_mul, one_mul]
end Formalism.FourierDecayAlt.P.Mx2
