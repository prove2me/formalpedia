-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.kappa_commute_l0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:32.090946+00:00
-- url     : https://prove2.me/submissions/878e55eb-f58a-4c18-bd03-f3f15fc2c210

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_sc

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
theorem _root_.solution (f : Ty P → ℂ) (Y : ℂ) : Commute (kap P f) (l0A P Y) := by
  unfold l0A nabA zbA ggiA
  exact ((kap_diag P f _).neg_right).sub_right
    ((Algebra.commute_algebraMap_right _ _).mul_right ((kap_sc P f _).mul_right (kap_sc P f _)))
end Formalism.FourierDecayAlt.P.Mx5
