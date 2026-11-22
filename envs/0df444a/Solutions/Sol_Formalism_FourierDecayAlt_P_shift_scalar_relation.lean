-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.shift_scalar_relation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:19:18.791156+00:00
-- url     : https://prove2.me/submissions/6e43e69d-8a57-492c-bbaf-322ec74e77e2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Mx4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.SSScalar := by
  intro P l w
  show SS P l * sc P w = sc P w * SS P l
  ext π' π
  simp only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]
  split_ifs
  · exact (Algebra.commutes _ _)
  · simp
end Formalism.FourierDecayAlt.P
