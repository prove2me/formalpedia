-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nabs_gg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:33.134674+00:00
-- url     : https://prove2.me/submissions/e8290fff-c3b2-4b25-8003-2262f376a4d5

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_GG_z
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_gg_zb
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
theorem _root_.solution (a TT : ℝ) : nabsE a TT * (ggP TT : Pr r) = ggP TT * nabsE a TT - zP := by
  rw [ggP, nabsE_fn, euler_GG_z, euler_gg_zb, zP]
  congr 2
  · field_simp [coord_ne r vzb]
  · field_simp [coord_ne r vz]
end Formalism.FourierDecayAlt.P.Mx2
