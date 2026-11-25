-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.dualCapV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:55:07.354049+00:00
-- url     : https://prove2.me/submissions/f837fbe6-566a-4925-a3ad-5358145dc5b1

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_dual_capacity_variant
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_dual_capacity_variant


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.DualCapV := Formalism.HermitianLatticeCounting.P.dual_capacity_variant
end Formalism.HermitianLatticeCounting.Final.S4
