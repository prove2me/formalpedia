-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.p_ci
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:58.176916+00:00
-- url     : https://prove2.me/submissions/9eba1fc4-7549-432c-83a6-97fe70e78ca6

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerCoord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_der_fn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_inv
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
theorem _root_.solution (l : Fin r) : pP l * ciP l = ciP l * pP l - ciP l := by
  rw [partialDeriv_def, ciP, der_fn, euler_inv _ _ (coord_ne r _), euler_inv _ _ (coord_ne r _), (eulerCoord r _ _ 0).1,
    (eulerCoord r _ _ 0).1, if_pos rfl, if_pos rfl, one_mul, one_mul, sub_eq_add_neg, multiplierPair_neg]
  congr 2
  · field_simp [coord_ne r (vc l)]
  · field_simp [coord_ne r (vcb l)]
end Formalism.FourierDecayAlt.P.Mx2
