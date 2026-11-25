-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.torus_action_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:40.253801+00:00
-- url     : https://prove2.me/submissions/2981f95f-cedc-4c2a-b263-f66697b7a0d9

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TorusArgumentMultiplicative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate InnerProductSpace ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.TaGroup := by
  intro a b φ ψ
  refine ⟨?_, ?_, ?_⟩
  · unfold C7.taS; rw [Complex.norm_exp]; simp
  · unfold C7.taS; rw [← Complex.exp_add]; congr 1; push_cast; ring
  · simp [C7.taS]
end Formalism.FourierDecayAlt.P
