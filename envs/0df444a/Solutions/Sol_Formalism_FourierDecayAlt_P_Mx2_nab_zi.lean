-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nab_zi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:58.884818+00:00
-- url     : https://prove2.me/submissions/e53371aa-b937-4733-b226-59ed5cebd879

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerCoord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabE_fn

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
theorem _root_.solution (a TT : ℝ) : nabE a TT * (ziP : Pr r) = ziP * nabE a TT - ziP * ziP := by
  rw [ziP, nabE_fn, euler_inv _ _ (coord_ne r _), euler_inv _ _ (coord_ne r _), (eulerCoord r vz vz 0).1,
    (eulerCoord r vzb vzb 0).1, if_pos rfl, if_pos rfl, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]
  congr 2
  · field_simp [coord_ne r vz]
  · field_simp [coord_ne r vzb]
end Formalism.FourierDecayAlt.P.Mx2
