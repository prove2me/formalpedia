-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.bridgeExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:57:08.29481+00:00
-- url     : https://prove2.me/submissions/7fed2b1b-8c08-46ee-a642-6f4c1bf3948c

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_self_dual_lattice_exists
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_self_dual_lattice_exists


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.BridgeExists := Formalism.HermitianLatticeCounting.P.self_dual_lattice_exists
end Formalism.HermitianLatticeCounting.Final.S4
