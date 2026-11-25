-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.dualCap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:55:01.130802+00:00
-- url     : https://prove2.me/submissions/663a1b7b-8209-4731-a96a-43a7d9ee6fb5

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_dual_capacity_formula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_dual_capacity_formula


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.DualCap := Formalism.HermitianLatticeCounting.P.dual_capacity_formula
end Formalism.HermitianLatticeCounting.Final.S4
