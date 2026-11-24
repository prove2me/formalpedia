-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.upper_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:51.836715+00:00
-- url     : https://prove2.me/submissions/56147bf2-ec07-472e-a026-257097a6e2e8

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {p : ℕ} (u : G.UT p → ℂ) (a b : Fin p) (h : b < a) : G.upper u a b = 0 := by
  simp [G.upper, G.strictUpper, ne_of_gt h, not_lt.mpr (le_of_lt h)]
end Formalism.FourierDecayAlt.P.Ux5
