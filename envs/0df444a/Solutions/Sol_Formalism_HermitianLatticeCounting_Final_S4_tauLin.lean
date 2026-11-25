-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.tauLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:59:54.52741+00:00
-- url     : https://prove2.me/submissions/013b732c-23d5-45de-b43d-34672dda426b

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_involution_map_linear
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_involution_map_linear


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.TauLin := Formalism.HermitianLatticeCounting.P.involution_map_linear
end Formalism.HermitianLatticeCounting.Final.S4
