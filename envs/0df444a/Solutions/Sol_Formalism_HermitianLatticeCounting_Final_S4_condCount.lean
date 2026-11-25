-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.condCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:57:20.646907+00:00
-- url     : https://prove2.me/submissions/56e0380c-b94d-4766-bf5e-4e91d207a5e2

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_conditional_count_formula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_conditional_count_formula


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.CondCount := Formalism.HermitianLatticeCounting.P.conditional_count_formula
end Formalism.HermitianLatticeCounting.Final.S4
