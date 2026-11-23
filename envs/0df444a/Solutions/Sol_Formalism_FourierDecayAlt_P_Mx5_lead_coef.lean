-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.lead_coef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:15.823497+00:00
-- url     : https://prove2.me/submissions/19558e1b-74f0-4333-9d4d-accf97575737

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_ggi_gg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_gg_def
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_gg_z_ggi

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
theorem _root_.solution : ggiA P * (kap P fun _ => -((P.T : ℂ) * P.T')) +
    ggA P * 1 * -(zA P * ggiA P) * -(zbA P * ggiA P) = 1 := by
  have h2 : zA P * ggiA P = ggiA P * zA P := by
    unfold zA ggiA zP ggiP
    exact fn_comm P _ _ _ _
  have h1 : zbA P * ggiA P = ggiA P * zbA P := by
    unfold zbA ggiA zbP ggiP
    exact fn_comm P _ _ _ _
  have hc : zA P * (zbA P * ggiA P) = ggiA P * (zA P * zbA P) := by
    rw [h1, ← mul_assoc, h2, mul_assoc]
  have hT : ((P.TT : ℝ) : ℂ) = (P.T : ℂ) * P.T' := by
    unfold Par.TT
    push_cast
    ring
  rw [kap_const, mul_one, mul_neg, mul_neg, neg_mul, neg_neg, gg_z_ggi, hc, ← ggi_gg P, gg_def, hT, mul_sub, map_neg, mul_neg]
  abel
end Formalism.FourierDecayAlt.P.Mx5
