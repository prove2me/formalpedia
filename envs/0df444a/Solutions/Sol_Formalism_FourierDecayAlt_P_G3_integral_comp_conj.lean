-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.integral_comp_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:11.303541+00:00
-- url     : https://prove2.me/submissions/757051ca-46b0-47d5-9ab3-a080b97d86fe

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P.G3
theorem _root_.solution (G : ℂ → ℂ) :
    ∫ ξ : ℂ, G ((starRingEnd ℂ) ξ) = ∫ η : ℂ, G η :=
  (Complex.conjLIE.measurePreserving).integral_comp
    Complex.conjLIE.toHomeomorph.measurableEmbedding G
end Formalism.FourierDecayAlt.P.G3
