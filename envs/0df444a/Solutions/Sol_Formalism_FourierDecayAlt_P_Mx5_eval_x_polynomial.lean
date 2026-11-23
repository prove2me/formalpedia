-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.eval_x_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:09.037795+00:00
-- url     : https://prove2.me/submissions/cdad0aed-c3f3-48a2-86ea-8f35e874c21a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar

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
theorem _root_.solution (π : Ty P) (Y : ℂ) : (coordinatePolynomial P π).eval Y = xC P π (Y + 1) := by
  unfold coordinatePolynomial xC
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  ring
end Formalism.FourierDecayAlt.P.Mx5
