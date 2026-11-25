-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.leakShare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:02:54.504437+00:00
-- url     : https://prove2.me/submissions/d1f30824-8126-4a8f-b3fe-9252c66ff4f7

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_leakage_share_bound_alt
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_leakage_share_bound_alt


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.LeakShare := Formalism.HermitianLatticeCounting.P.leakage_share_bound_alt
end Formalism.HermitianLatticeCounting.Final.S4
