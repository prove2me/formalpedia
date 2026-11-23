-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.euler_GG_z
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:26.954794+00:00
-- url     : https://prove2.me/submissions/0d152824-62ad-4f65-a6d6-d376481ac4bf

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_eulerLeibniz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_eulerCoord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_vz_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (TT : ℝ) : euler vz (gg TT : Fn r) = coord vz * coord vzb := by
  unfold gg
  rw [map_sub, eulerLeibniz, (eulerCoord r vz vz 0).1, (eulerCoord r vz vzb 0).1, (eulerCoord r vz vz _).2,
    if_pos rfl, if_neg vz_ne]; simp
end Formalism.FourierDecayAlt.P.Mx4
