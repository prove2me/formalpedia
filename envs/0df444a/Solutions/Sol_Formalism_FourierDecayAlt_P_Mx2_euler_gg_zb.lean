-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.euler_gg_zb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:37.155633+00:00
-- url     : https://prove2.me/submissions/0766e56b-9b35-423c-8a23-f2d59fc20d59

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerLeibniz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerCoord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_vz_ne

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
theorem _root_.solution (TT : ℝ) : euler vzb (gg TT : Fn r) = coord vz * coord vzb := by
  unfold gg
  rw [map_sub, eulerLeibniz, (eulerCoord r vzb vz 0).1, (eulerCoord r vzb vzb 0).1, (eulerCoord r vzb vz _).2,
    if_pos rfl, if_neg vz_ne.symm]; simp
end Formalism.FourierDecayAlt.P.Mx2
