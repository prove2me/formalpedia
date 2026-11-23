-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.diag_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:11.034798+00:00
-- url     : https://prove2.me/submissions/03e21596-8961-43b6-a87d-2dd3c3a54dbd

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_sss_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_rho_up_same

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
theorem _root_.solution {l : ℕ} (hN : star (SS P l) * SS P l = kap P fun π => ((Nrm P l π : ℝ) : ℂ)) (Y : ℂ)
    (hl : l ∈ Icc 1 (P.k - 1)) :
    (kap P fun π => xEx P {l} π Y) * star (SS P l) * ((kap P fun π => (Y + (rho P π l : ℂ))⁻¹) * SS P l) =
      kap P fun π => xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by
  have hs := sss_shift P l (fun π => (Y + (rho P π l : ℂ) + 1)⁻¹) (fun π => (Y + (rho P π l : ℂ))⁻¹)
    (fun π π' h => by
      beta_reduce
      rw [rho_up_same P hl h]
      push_cast
      ring)
  rw [← mul_assoc, mul_assoc (kap P _) (star (SS P l)), hs, ← mul_assoc, mul_assoc _ (star (SS P l)), hN,
    ← kap_mul, ← kap_mul]
  refine congrArg (kap P) (funext fun π => ?_)
  ring
end Formalism.FourierDecayAlt.P.Mx5
