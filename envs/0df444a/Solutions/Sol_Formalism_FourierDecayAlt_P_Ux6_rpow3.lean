-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.rpow3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:39:37.063918+00:00
-- url     : https://prove2.me/submissions/6514274a-f5cf-4ef0-a336-bc2b0d914da4

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
theorem _root_.solution {A B W a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    (A * B * W) ^ (-a) = (A ^ (-a) * B ^ (-a)) * W ^ (-a) := by
  rw [Real.mul_rpow (by positivity) hW, Real.mul_rpow hA hB]
end Formalism.FourierDecayAlt.P.Ux6
