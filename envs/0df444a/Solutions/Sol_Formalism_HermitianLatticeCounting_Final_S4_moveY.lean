-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.moveY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:11:11.395197+00:00
-- url     : https://prove2.me/submissions/564078e5-8880-4e94-b981-836f662a9ef8

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_move_second_coordinate
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_move_second_coordinate


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.MoveY := Formalism.HermitianLatticeCounting.P.move_second_coordinate
end Formalism.HermitianLatticeCounting.Final.S4
