-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.lca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:25.001955+00:00
-- url     : https://prove2.me/submissions/054a3ad1-0c6d-4475-8cce-73e9a452f848

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt

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
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution {a b p q : B} (h : a * b = b * a + p * q) (x : B) : a * (b * x) = b * (a * x) + p * (q * x) := by
  rw [← mul_assoc, h, add_mul, mul_assoc, mul_assoc]
end Formalism.FourierDecayAlt.P.Mx6
