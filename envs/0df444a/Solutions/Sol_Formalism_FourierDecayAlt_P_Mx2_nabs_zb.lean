-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nabs_zb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:00.366815+00:00
-- url     : https://prove2.me/submissions/a40b05d4-3100-4e6a-a7c1-ab1af26fb58d

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerCoord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabsE_fn

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
theorem _root_.solution (a TT : ℝ) : nabsE a TT * (zbP : Pr r) = zbP * nabsE a TT - 1 := by
  rw [zbP, nabsE_fn, (eulerCoord r vz vz 0).1, (eulerCoord r vzb vzb 0).1, if_pos rfl, if_pos rfl,
    inv_mul_cancel₀ (coord_ne r _), inv_mul_cancel₀ (coord_ne r _), multiplierPair_one]
end Formalism.FourierDecayAlt.P.Mx2
