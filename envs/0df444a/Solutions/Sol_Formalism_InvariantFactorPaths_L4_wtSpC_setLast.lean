-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wtSpC_setLast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:16:45.06926+00:00
-- url     : https://prove2.me/submissions/86e9d699-4a65-4b64-bf41-677f845bbbfa

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (o j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    WtSpC p (setLast LL o) j Cs la = WtSpC p LL j Cs la := rfl
end Formalism.InvariantFactorPaths.L4
