-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.share_first_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:03:30.852889+00:00
-- url     : https://prove2.me/submissions/0a55f83f-6c6d-410a-820d-58f7273810fb

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_shared_constant_formula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_shared_constant_formula


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.LocalDensityShareBound := Formalism.HermitianLatticeCounting.P.shared_constant_formula
end Formalism.HermitianLatticeCounting.Final.S4
