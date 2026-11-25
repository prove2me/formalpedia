-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.pairing_orthogonal_complement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:10:26.007286+00:00
-- url     : https://prove2.me/submissions/d7acbf4f-d35d-41f1-b46b-7bf30b12ab74

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_pair_second_constant
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pair_second_constant


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.PairingOrthogonalComplement := Formalism.HermitianLatticeCounting.P.pair_second_constant
end Formalism.HermitianLatticeCounting.Final.S4
