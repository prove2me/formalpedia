-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.esI_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:50:33.898912+00:00
-- url     : https://prove2.me/submissions/18dabbd4-31f3-405f-8f0a-a596335083f6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (b : Fin r) : (esI k r b).val = 2 * r + k - b.val := rfl
end Formalism.FourierDecayAlt.P.SignAntidiagonal
