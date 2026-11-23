-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.fn_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:25.73394+00:00
-- url     : https://prove2.me/submissions/f9eb64c5-b22b-4800-8264-a1fdca8eee70

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
theorem _root_.solution (f fb g gb : Fn P.r) : Commute (sc P (fnP f fb)) (sc P (fnP g gb)) := by
  have key : ∀ a b : Fn P.r, mulOp a * mulOp b = mulOp b * mulOp a := by
    intro a b
    apply LinearMap.ext
    intro x
    simp only [mulOp, Module.End.mul_apply, LinearMap.mulLeft_apply]
    ring
  unfold sc
  apply Commute.map _ (Matrix.scalar (Ty P))
  unfold fnP Formalism.FourierDecayAlt.M.mk
  exact Prod.ext (key f g) (congrArg MulOpposite.op (key gb fb))
end Formalism.FourierDecayAlt.P.Mx5
