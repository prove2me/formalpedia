-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.moveWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:10:40.891491+00:00
-- url     : https://prove2.me/submissions/637800eb-03ab-44e9-9153-8a69cc787065

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_move_preserves_weight
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_move_preserves_weight


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.MoveWeight := Formalism.HermitianLatticeCounting.P.move_preserves_weight
end Formalism.HermitianLatticeCounting.Final.S4
