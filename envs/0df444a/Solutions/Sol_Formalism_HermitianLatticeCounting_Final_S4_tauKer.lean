-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.tauKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:59:48.171304+00:00
-- url     : https://prove2.me/submissions/a2f88aaf-0e77-45d7-bce0-6d1ae8f0184f

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_involution_kernel
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_involution_kernel


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.TauKer := Formalism.HermitianLatticeCounting.P.involution_kernel
end Formalism.HermitianLatticeCounting.Final.S4
