-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.x_iv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:21.543143+00:00
-- url     : https://prove2.me/submissions/3146b7b6-1fb4-4928-bd42-4bfe523d70ad

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_xC_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fac_ne

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
theorem _root_.solution (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) (j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) :
    xA P Y * (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) = kap P fun π => xEx P {j} π Y := by
  unfold xA
  rw [← kap_mul]
  congr 1
  funext π
  rw [xC_split P j hj π Y, mul_right_comm, mul_inv_cancel₀ (fac_ne P (hx π) hj), one_mul]
end Formalism.FourierDecayAlt.P.Mx5
