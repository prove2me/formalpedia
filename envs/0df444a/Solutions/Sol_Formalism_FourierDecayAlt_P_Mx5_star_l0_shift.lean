-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.star_l0_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:24.457954+00:00
-- url     : https://prove2.me/submissions/c8089232-4dda-4003-a9b7-8d1c82eea147

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_gg_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_nabs_gg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_raising_constant_eq_nabla_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_block_frame_conjugation_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_lowering_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_GG_commute_z
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_gamma_inv_commute_zeta
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
theorem _root_.solution (Y : ℂ) (hY : star Y = Y) : star (l0A P (Y - 1)) = m0A P Y := by
  rw [star_lowering_constant, star_sub, hY, star_one, raising_constant_eq_nabla_star, raising_constant_eq_nabla_star,
    block_frame_conjugation_identity (ggA P) (ggiA P) (zA P) (nabsA P) (Y - 1 - 1 / 2) 1 (gg_ggi P) (by rw [nabs_gg, one_smul])
      (GG_commute_z P).symm (gamma_inv_commute_zeta P).symm, gamma_inv_commute_zeta P, show Y - 1 - 1 / 2 + 1 = Y - 1 / 2 by ring]
end Formalism.FourierDecayAlt.P.Mx5
