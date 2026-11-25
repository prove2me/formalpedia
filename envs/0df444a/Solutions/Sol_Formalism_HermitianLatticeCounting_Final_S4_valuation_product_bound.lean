-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.valuation_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:10:29.458006+00:00
-- url     : https://prove2.me/submissions/a3fa8e5c-846d-49c4-9193-b016a8f6920a

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_local_density_product
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_local_density_product


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.ValuationProductBound := Formalism.HermitianLatticeCounting.P.local_density_product
end Formalism.HermitianLatticeCounting.Final.S4
