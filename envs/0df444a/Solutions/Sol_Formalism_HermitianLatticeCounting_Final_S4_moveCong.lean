-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.moveCong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:56:16.158775+00:00
-- url     : https://prove2.me/submissions/eea2f921-853a-470d-8dae-d1efc656545a

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_move_congruence
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_move_congruence


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.MoveCong := Formalism.HermitianLatticeCounting.P.move_congruence
end Formalism.HermitianLatticeCounting.Final.S4
