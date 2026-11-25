-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.schur_product_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:55:01.615568+00:00
-- url     : https://prove2.me/submissions/7bada8a4-93a5-4532-85e4-b88b7b8b1475

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
theorem _root_.solution : C7.SchurProductPSD := by
  intro ι _ _ A C hA hC
  exact hA.hadamard hC
end Formalism.FourierDecayAlt.P
