-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.star_t12
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:27.727817+00:00
-- url     : https://prove2.me/submissions/212c57b1-72fa-4509-9cda-1706c06a7e58

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_gg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_raising_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kappa_commute_l0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_xC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_upper_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_ggi_kap_gg

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
theorem _root_.solution (Y : ℂ) : star (t12 P Y) = t21 P (star Y) := by
  unfold t21 t12 xA
  rw [star_add, star_mul, star_mul, star_raising_constant, star_kap, star_gg, star_upper_sum]
  simp only [star_xC]
  rw [add_left_inj]
  rw [mul_assoc (ggA P * l0A P (star Y)), ggi_kap_gg, mul_assoc, mul_assoc, (kappa_commute_l0 P _ _).eq]
end Formalism.FourierDecayAlt.P.Mx5
