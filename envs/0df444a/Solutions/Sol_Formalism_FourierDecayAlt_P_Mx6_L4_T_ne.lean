-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L4.T_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:30.044812+00:00
-- url     : https://prove2.me/submissions/dc7213fc-9d24-45a6-8b98-f465b24aec3c

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_S_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_xEx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_xEx_rr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_E_Ss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.L4
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.L4
theorem _root_.solution {u : ℂ} (hu : Good P u) {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ l) :
    (kap P fun π => xEx P {l} π u) * star (SS P l) * (kap P (rr P j u) * SS P j) =
      star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π u := by
  have h1 : kap P ((fun π => xEx P {l} π u) * rr P j u) * SS P j = SS P j * kap P fun π => xEx P {l, j} π u :=
    S_shift P j (fun π => xEx P {l, j} π u) ((fun π => xEx P {l} π u) * rr P j u) fun π π' h => by
      rw [Pi.mul_apply, xEx_rr P hu hj hne, xEx_up P h {l, j} (by simp)]
  rw [E_Ss, mul_assoc, ← mul_assoc (kap P _) (kap P _), kap_mul, h1, mul_assoc]
end Formalism.FourierDecayAlt.P.Mx6.L4
