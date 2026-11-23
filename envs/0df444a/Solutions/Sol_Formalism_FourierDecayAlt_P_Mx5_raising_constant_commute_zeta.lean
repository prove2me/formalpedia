-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.raising_constant_commute_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:06.020922+00:00
-- url     : https://prove2.me/submissions/cca61ec6-e4e1-4cee-9935-ce0f19077aa7

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_nabs_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_raising_constant_eq_nabla_star

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
theorem _root_.solution (Y : ℂ) : Commute (m0A P Y) (zA P) := by
  rw [raising_constant_eq_nabla_star]
  have hn : Commute (nabsA P) (zA P) := nabs_alt P
  have h2 : Commute (zA P * ggiA P) (zA P) := (Commute.refl _).mul_left (by
    unfold ggiA zA ggiP zP
    exact fn_comm P _ _ _ _)
  exact hn.neg_left.sub_left (h2.smul_left _)
end Formalism.FourierDecayAlt.P.Mx5
