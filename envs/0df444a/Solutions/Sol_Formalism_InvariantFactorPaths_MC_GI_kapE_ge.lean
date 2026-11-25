-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.MC.GI.kapE_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:27.397344+00:00
-- url     : https://prove2.me/submissions/1fb13e81-9154-4872-9644-ab35f56bbdd9

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMCB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_GamIntC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.MC Formalism.InvariantFactorPaths.MC.GI
open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.InvariantFactorPaths.MC.GI
theorem _root_.solution (N r B : ℕ) (_hr : 1 ≤ r) : (N + 4) * (r * B) + 6 * B ≤ kapE N r B := by
  exact le_refl _
end Formalism.InvariantFactorPaths.MC.GI
