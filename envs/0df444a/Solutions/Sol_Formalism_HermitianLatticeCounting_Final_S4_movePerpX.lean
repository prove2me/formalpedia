-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.movePerpX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:56:31.522432+00:00
-- url     : https://prove2.me/submissions/cbf0638e-14e7-47a5-8682-20ae393a17fc

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_move_perpendicular_extended
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_move_perpendicular_extended


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.MovePerpX := Formalism.HermitianLatticeCounting.P.move_perpendicular_extended
end Formalism.HermitianLatticeCounting.Final.S4
