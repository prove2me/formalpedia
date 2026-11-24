-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.le_div_of_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:37:55.778232+00:00
-- url     : https://prove2.me/submissions/60d3cf97-8340-4484-bbed-55aa8a5caa9d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution {X C y m m0 : ℝ} (hy : 0 ≤ y) (hm0 : 0 < m0) (hm : m0 ≤ m) (h : X ≤ C * y / m) :
    X ≤ max C 0 / m0 * y := by
  have hm' : 0 < m := lt_of_lt_of_le hm0 hm
  have hD : 0 ≤ max C 0 := le_max_right _ _
  calc X ≤ C * y / m := h
    _ ≤ max C 0 * y / m := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hy) hm'.le
    _ ≤ max C 0 * y / m0 := div_le_div_of_nonneg_left (mul_nonneg hD hy) hm0 hm
    _ = max C 0 / m0 * y := by ring
end Formalism.FourierDecayAlt.P.Ux6
