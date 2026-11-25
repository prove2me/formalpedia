-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.unfoldSym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:00:29.804865+00:00
-- url     : https://prove2.me/submissions/7d0b2850-64cd-484b-a4f9-69140ef0f8a2

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unfolding_symmetric
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_unfolding_symmetric


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S4
namespace Formalism.HermitianLatticeCounting.Final.S4
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.UnfoldSym := Formalism.HermitianLatticeCounting.P.unfolding_symmetric
end Formalism.HermitianLatticeCounting.Final.S4
