-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.annihSize
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:04:08.351193+00:00
-- url     : https://prove2.me/submissions/2e7477b2-b4d9-4567-abb5-24d69475d165

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_annihilator_size
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_annihilator_size


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.AnnihSize := Formalism.HermitianLatticeCounting.P.annihilator_size
end Formalism.HermitianLatticeCounting.Final.S4
