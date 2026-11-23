-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.qQLeading
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:06.648843+00:00
-- url     : https://prove2.me/submissions/f07a7129-17cb-4490-8008-5693e5f61cdf

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_coeff_t22
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_term_lower_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_coeff_t12
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_leading_coeff_t11

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
theorem _root_.solution : QQLeading := by
  intro P hP
  obtain ⟨a11, h11⟩ := leading_coeff_t11 P hP
  obtain ⟨a12, h12⟩ := leading_coeff_t12 P hP.k_pos
  obtain ⟨a21, h21⟩ := leading_term_lower_left P hP.k_pos
  obtain ⟨a22, h22⟩ := leading_coeff_t22 P
  refine ⟨a11, a12, a21, a22, fun Y => ⟨h11 Y, ?_, ?_, h22 Y⟩⟩
  · rw [h12, smul_neg]
  · rw [h21, smul_neg]
end Formalism.FourierDecayAlt.P.Mx5
