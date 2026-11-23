-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.euler_GG_z
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:37.098859+00:00
-- url     : https://prove2.me/submissions/01331690-5e69-4ba2-abdf-6326421f98cc

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
theorem _root_.solution (TT : ℝ) : euler vz (gg TT : Fn r) = coord vz * coord vzb := by
  unfold gg
  rw [map_sub, eulerLeibniz, (eulerCoord r vz vz 0).1, (eulerCoord r vz vzb 0).1, (eulerCoord r vz vz _).2,
    if_pos rfl, if_neg vz_ne]; simp
end Formalism.FourierDecayAlt.P.Mx2
