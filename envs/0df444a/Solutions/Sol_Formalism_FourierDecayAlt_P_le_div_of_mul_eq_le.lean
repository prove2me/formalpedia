-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.le_div_of_mul_eq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:03.475423+00:00
-- url     : https://prove2.me/submissions/024ca0fb-fb92-4270-be14-9d2f57dee880

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UpperMinorIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetSubmatrixUnitriangularEqOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeDivOfMulEqLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 EntryMinorBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (x c D Kb : ℝ) (hc : 0 < c) (hD : D ≤ Kb) (h : x * c = D) : x ≤ Kb / c := by
  rw [le_div_iff₀ hc, h]; exact hD
end Formalism.FourierDecayAlt.P
