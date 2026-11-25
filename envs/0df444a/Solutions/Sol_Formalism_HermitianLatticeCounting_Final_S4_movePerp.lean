-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.movePerp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:56:27.036174+00:00
-- url     : https://prove2.me/submissions/a7636d0a-d179-4f40-b5e0-c8d14db0f80c

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_move_perpendicular
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_move_perpendicular


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.MovePerp := Formalism.HermitianLatticeCounting.P.move_perpendicular
end Formalism.HermitianLatticeCounting.Final.S4
