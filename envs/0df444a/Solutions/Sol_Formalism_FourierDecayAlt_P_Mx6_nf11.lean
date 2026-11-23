-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.nf11
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:28.842798+00:00
-- url     : https://prove2.me/submissions/e95af9ae-1318-4296-afed-86a9cfce7da9

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lA_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_wC_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_xLam
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_L4_upper_sum_mul_lambda
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_absN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_nf12
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_coordinate_commute_raising_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_S12_commute_GGinv

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (hN : SSNorm) (hP : P.OK) {u : ℂ} (hu : Good P u) :
    t11 P u = dA P u + mt P u * t22 P u * lA P u := by
  rw [← nf12 P hu, t12, lA_eq, absN _ _ _ _ _ _ _ (coordinate_commute_raising_constant P u u) (kap_G P _) (S12_commute_GGinv P u), L4.xLam P hu,
    L4.upper_sum_mul_lambda P hP hu hN, t11, mul_add]
  have e : ggiA P * (kap P fun π => wC P π u) = dA P u + ggiA P * kap P fun π =>
      ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
    rw [dA, ← mul_smul_comm, ← map_smul, ← mul_add, ← map_add]
    congr 2
    funext π
    rw [WB.wC_eq P hP π u hu]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  rw [e]
  abel
end Formalism.FourierDecayAlt.P.Mx6
