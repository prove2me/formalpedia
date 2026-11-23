-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.xC_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:33.9209+00:00
-- url     : https://prove2.me/submissions/df4ab00e-04f0-44e2-a306-321faf2f1511

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
theorem _root_.solution (j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (π : Ty P) (Y : ℂ) :
    xC P π Y = (Y + (rho P π j : ℂ)) * xEx P {j} π Y := by
  unfold xC xEx
  rw [Finset.sdiff_singleton_eq_erase]
  exact (Finset.mul_prod_erase _ (fun i => Y + (rho P π i : ℂ)) hj).symm
end Formalism.FourierDecayAlt.P.Mx5
