-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.absCC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:53.61092+00:00
-- url     : https://prove2.me/submissions/3bdfa3c2-64b8-4223-8753-28e247f59855

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
theorem _root_.solution (a b K1 K2 : B) (hab : a * b = b * a) (hK : K1 * K2 = K2 * K1) (h1 : K1 * b = b * K1)
    (h2 : K2 * a = a * K2) : (a * K1) * (b * K2) = (b * K2) * (a * K1) :=
  calc a * K1 * (b * K2) = a * b * (K1 * K2) := by rw [mul_assoc, lc h1, mul_assoc]
    _ = b * a * (K2 * K1) := by rw [hab, hK]
    _ = b * K2 * (a * K1) := by rw [mul_assoc b K2, lc h2, mul_assoc]
end Formalism.FourierDecayAlt.P.Mx6
