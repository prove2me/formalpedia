-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.primCancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:59:26.738328+00:00
-- url     : https://prove2.me/submissions/dd5c2033-f5e1-4e6e-a85e-c2afaf0576ff

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_primitive_cancellation
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_primitive_cancellation


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.PrimCancel := Formalism.HermitianLatticeCounting.P.primitive_cancellation
end Formalism.HermitianLatticeCounting.Final.S4
