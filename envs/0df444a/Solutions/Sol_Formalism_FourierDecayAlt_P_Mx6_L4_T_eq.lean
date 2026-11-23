-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.L4.T_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:25.226784+00:00
-- url     : https://prove2.me/submissions/59373786-de2a-440b-aa9f-10970ec2cdd0

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_S_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_xEx_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_rr_up_same
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
theorem _root_.solution (hP : P.OK) (hN : SSNorm) (u : ℂ) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) :
    (kap P fun π => xEx P {l} π u) * star (SS P l) * (kap P (rr P l u) * SS P l) =
      kap P fun π => ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
  have h1 : kap P ((fun π => xEx P {l} π u) * rr P l u) * SS P l =
      SS P l * kap P ((fun π => xEx P {l} π u) * rr1 P l u) :=
    S_shift P l ((fun π => xEx P {l} π u) * rr1 P l u) ((fun π => xEx P {l} π u) * rr P l u) fun π π' h => by
      rw [Pi.mul_apply, Pi.mul_apply, xEx_up P h {l} (by simp), rr_up_same P hl h]
  rw [E_Ss, mul_assoc, ← mul_assoc (kap P _) (kap P _), kap_mul, h1, ← mul_assoc, (hN P hP l hl).1, kap_mul]
  congr 1
  funext π
  simp only [Pi.mul_apply, rr1]
  rw [div_eq_mul_inv, mul_assoc]
end Formalism.FourierDecayAlt.P.Mx6.L4
