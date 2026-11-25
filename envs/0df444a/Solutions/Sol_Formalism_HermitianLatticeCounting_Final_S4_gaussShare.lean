-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.gaussShare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:55:18.846139+00:00
-- url     : https://prove2.me/submissions/78df355b-1355-47ba-be64-dd17d29dbded

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_gauss_sum_share
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gauss_sum_share


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.GaussShare := Formalism.HermitianLatticeCounting.P.gauss_sum_share
end Formalism.HermitianLatticeCounting.Final.S4
