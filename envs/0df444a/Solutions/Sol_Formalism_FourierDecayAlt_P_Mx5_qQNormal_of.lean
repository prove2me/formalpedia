-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.qQNormal_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:47.098798+00:00
-- url     : https://prove2.me/submissions/4c071727-6146-4c0b-84ff-87ce9056e131

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lower_left_normal_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_upper_right_normal_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_upper_left_normal_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_mA_star

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
theorem _root_.solution (hN : SSNorm) : QQNormal := by
  intro P hP Y hx
  have hN' : ∀ l ∈ Icc 1 (P.k - 1), star (SS P l) * SS P l = kap P fun π => ((Nrm P l π : ℝ) : ℂ) :=
    fun l hl => (hN P hP l hl).1
  exact ⟨lower_left_normal_form P Y hx, upper_right_normal_form P Y hx, fun hx1 => upper_left_normal_form P hP hN' Y hx hx1,
    fun hY => mA_star P Y hY⟩
end Formalism.FourierDecayAlt.P.Mx5
