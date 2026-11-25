-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.divisorCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:57:31.83715+00:00
-- url     : https://prove2.me/submissions/4594f73c-9508-4291-ad9f-ee318c7cb5bd

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_divisor_count_bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_divisor_count_bound


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.DivisorCount := Formalism.HermitianLatticeCounting.P.divisor_count_bound
end Formalism.HermitianLatticeCounting.Final.S4
