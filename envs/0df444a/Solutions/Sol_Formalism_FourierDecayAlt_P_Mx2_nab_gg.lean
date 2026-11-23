-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nab_gg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:40.077957+00:00
-- url     : https://prove2.me/submissions/d1824d2a-018e-458c-acd5-a70404adb73c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_GG_z
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_gg_zb
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
theorem _root_.solution (a TT : ℝ) : nabE a TT * (ggP TT : Pr r) = ggP TT * nabE a TT + zbP := by
  rw [ggP, nabE_fn, euler_GG_z, euler_gg_zb, zbP]
  congr 2
  · field_simp [coord_ne r vz]
  · field_simp [coord_ne r vzb]
end Formalism.FourierDecayAlt.P.Mx2
