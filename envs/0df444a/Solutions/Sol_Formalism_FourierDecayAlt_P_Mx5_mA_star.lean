-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.mA_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:29.56697+00:00
-- url     : https://prove2.me/submissions/8c0e0f6a-a1d3-4c12-89f8-9a750cd9fd10

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_kap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_sss_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_sss_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_ggi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_rho_up_same
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_star_l0_shift

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
theorem _root_.solution (Y : ℂ) (hY : star Y = Y) : mA P Y = star (lA P (Y - 1)) := by
  have hY' : (starRingEnd ℂ) Y = Y := hY
  unfold mA lA
  rw [star_add, star_l0_shift P Y hY, star_mul, star_ggi, star_sum, Finset.sum_mul, Finset.mul_sum,
    add_right_inj]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [star_mul, star_kap]
  have hs := sss_shift P j (fun π => (Y + (rho P π j : ℂ))⁻¹) (fun π => star ((Y - 1 + (rho P π j : ℂ))⁻¹))
    (fun π π' h => by
      beta_reduce
      rw [rho_up_same P hj h]
      simp [hY, hY', Complex.conj_ofReal]
      try ring)
  rw [hs]
  unfold ggiA
  exact ((kap_sc P _ _).mul_left (sss_sc P j _)).eq.symm
end Formalism.FourierDecayAlt.P.Mx5
