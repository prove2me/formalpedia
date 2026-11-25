-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.hermGaussRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:08:15.900921+00:00
-- url     : https://prove2.me/submissions/eda80bf4-c6ec-46b1-88de-51ab6ae6d233

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hermitian_gauss_sum_ring
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hermitian_gauss_sum_ring


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.HermGaussRing := Formalism.HermitianLatticeCounting.P.hermitian_gauss_sum_ring
end Formalism.HermitianLatticeCounting.Final.S4
