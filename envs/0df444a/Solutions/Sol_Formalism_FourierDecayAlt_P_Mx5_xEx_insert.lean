-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.xEx_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:23.082402+00:00
-- url     : https://prove2.me/submissions/fabd3195-7cb7-41b3-9454-7aa64fb6fb44

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
theorem _root_.solution (ex : Finset ℕ) (a : ℕ) (ha : a ∈ Icc 1 (P.k - 1) \ ex) (π : Ty P) (Y : ℂ) :
    xEx P ex π Y = (Y + (rho P π a : ℂ)) * xEx P (insert a ex) π Y := by
  unfold xEx
  rw [Finset.sdiff_insert]
  exact (Finset.mul_prod_erase _ (fun i => Y + (rho P π i : ℂ)) ha).symm
end Formalism.FourierDecayAlt.P.Mx5
