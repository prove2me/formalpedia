-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.absN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:41.864678+00:00
-- url     : https://prove2.me/submissions/b5e14ec6-3135-4c4b-9c59-4dc78a6a8a44

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_lc

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
theorem _root_.solution (g G X m0 l0 S12 L : B) (hXm : X * m0 = m0 * X) (hXG : X * G = G * X) (hSG : S12 * G = G * S12) :
    (g * X * m0 + S12) * (l0 + G * L) = g * X * m0 * l0 + g * m0 * G * (X * L) + S12 * l0 + G * (S12 * L) := by
  simp only [mul_add, add_mul, mul_assoc, lc hXm, lc hXG, lc hSG]
  abel
end Formalism.FourierDecayAlt.P.Mx6
