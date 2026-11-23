-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.absSand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:42.154354+00:00
-- url     : https://prove2.me/submissions/4b2195f6-abff-4b65-bfd5-4b545574798a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc1

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
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (g G K1 K2 K3 : B) (hgG : g * G = 1) (hGg : G * g = 1)
    (h1 : K1 * G = G * K1) (h2 : K2 * G = G * K2) (h1g : K1 * g = g * K1) (h2g : K2 * g = g * K2) :
    g * K1 * (K2 * (G * G)) * (g * K3) = K1 * K2 * K3 := by
  simp only [mul_assoc, lc h1, lc h2, lc1 hgG, lc1 hGg, lc h1g, lc h2g]
end Formalism.FourierDecayAlt.P.Mx6
