-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.leakBack
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:02:44.729156+00:00
-- url     : https://prove2.me/submissions/d59cb4ba-451b-42ed-be2d-7409e7cf4dae

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_leakage_back_map
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_leakage_back_map


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.LeakBack := Formalism.HermitianLatticeCounting.P.leakage_back_map
end Formalism.HermitianLatticeCounting.Final.S4
