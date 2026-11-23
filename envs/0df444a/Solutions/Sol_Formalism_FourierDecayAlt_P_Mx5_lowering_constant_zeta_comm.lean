-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.lowering_constant_zeta_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:55.467809+00:00
-- url     : https://prove2.me/submissions/09ae7f8f-83a5-4057-b29e-59612bcceff0

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_nabla_zeta_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_l0_eq_neg_nabla_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabla_zeta_comm


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
theorem _root_.solution (Y : ℂ) : l0A P Y * zA P = zA P * l0A P Y - 1 := by
  have hc : (zbA P * ggiA P) * zA P = zA P * (zbA P * ggiA P) := by
    have h1 : Commute (zbA P) (zA P) := by
      unfold zbA zA zbP zP
      exact fn_comm P _ _ _ _
    have h2 : Commute (ggiA P) (zA P) := by
      unfold ggiA zA ggiP zP
      exact fn_comm P _ _ _ _
    exact (h1.mul_left h2).eq
  rw [l0_eq_neg_nabla_sub, sub_mul, mul_sub, neg_mul, mul_neg, nabla_zeta_comm, smul_mul_assoc, hc, mul_smul_comm]
  abel
end Formalism.FourierDecayAlt.P.Mx5
