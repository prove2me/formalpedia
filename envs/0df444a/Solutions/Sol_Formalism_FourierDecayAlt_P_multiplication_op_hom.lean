-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.multiplication_op_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:13.693789+00:00
-- url     : https://prove2.me/submissions/47873694-ea9a-4a9a-8fc1-994a42226c4a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom

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
open Mx1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.M.MulOpHom := by
  intro r f g z
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine LinearMap.ext fun x => ?_ <;>
    simp [mulOp, mul_assoc, add_mul, Algebra.smul_def]
end Formalism.FourierDecayAlt.P
