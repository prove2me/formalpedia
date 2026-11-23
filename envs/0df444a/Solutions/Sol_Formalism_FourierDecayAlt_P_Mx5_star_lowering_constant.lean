-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.star_lowering_constant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:53.37897+00:00
-- url     : https://prove2.me/submissions/bee6ac6d-92c9-4d41-8c06-cb77b2ec3238

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_gg_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_nabs_gg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_zb
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_nab
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_l0_eq_neg_nabla_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_raising_constant_eq_nabla_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_block_frame_conjugation_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_half
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabs_gg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (Y : ℂ) : star (l0A P Y) = ggA P * m0A P (star Y) * ggiA P := by
  rw [raising_constant_eq_nabla_star, block_frame_conjugation_identity (ggA P) (ggiA P) (zA P) (nabsA P) (star Y - 1 / 2) 1 (gg_ggi P)
    (by rw [nabs_gg, one_smul]) (by unfold zA ggA zP ggP; exact fn_comm P _ _ _ _) (by unfold zA ggiA zP ggiP; exact fn_comm P _ _ _ _),
    l0_eq_neg_nabla_sub, star_sub, star_neg, star_smul, star_mul, star_nab, star_ggi, star_zb,
    show star (Y + 1 / 2 : ℂ) = star Y - 1 / 2 + 1 by rw [star_add, star_half]; ring]
end Formalism.FourierDecayAlt.P.Mx5
