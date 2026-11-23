-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nab_ggi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:58.274817+00:00
-- url     : https://prove2.me/submissions/7ddda8b5-8aac-4150-8772-0b41b6a341cc

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_GG_z
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_gg_zb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_gg_ne
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
theorem _root_.solution (a TT : ℝ) : nabE a TT * (ggiP TT : Pr r) = ggiP TT * nabE a TT - zbP * ggiP TT * ggiP TT := by
  rw [ggiP, nabE_fn, euler_inv _ _ (gg_ne TT), euler_inv _ _ (gg_ne TT), euler_GG_z, euler_gg_zb, zbP, multiplierPair_mul, multiplierPair_mul,
    sub_eq_add_neg, multiplierPair_neg]
  congr 2
  · field_simp [coord_ne r vz]
  · field_simp [coord_ne r vzb]
end Formalism.FourierDecayAlt.P.Mx2
