-- Prove2me | solution 1 for Formalism.DivisorInequality.UniformCovolumeTail.cvE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:40:40.629799+00:00
-- url     : https://prove2.me/submissions/33f47568-db34-496c-9ff6-90c92c6e818f

import Mathlib
import Definitions.Def_Formalism_DivisorInequality_DivIneqTopAnchorU
import Definitions.Def_Formalism_DivisorInequality_DivisorInequalityProofs_BaseLevelBoundsWithCovolumeHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramTopExact
import Definitions.Def_Formalism_DivisorInequality_DivisorInequalityProofs_EvenDegreeWeightBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open scoped Matrix ComplexOrder
open Formalism Formalism.DivisorInequality
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisorInequality.UniformCovolumeTail
namespace Formalism.DivisorInequality.UniformCovolumeTail
theorem _root_.solution (Cb ce X B0 l2 Nc : ℝ) (hX : 0 < X) :
    Cb * (ce * X) * (B0 + l2 * Nc / X) = Cb * (ce * (X * B0 + l2 * Nc)) := by
  have e : X * X⁻¹ = 1 := mul_inv_cancel₀ hX.ne'
  linear_combination (Cb * ce * l2 * Nc) * e
end Formalism.DivisorInequality.UniformCovolumeTail
