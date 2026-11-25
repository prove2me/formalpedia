-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.hermGaussCond
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:00:17.537888+00:00
-- url     : https://prove2.me/submissions/0cb1df02-a4ad-47ab-8835-0fd5550cfe3d

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hermitian_gauss_condition
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hermitian_gauss_condition


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.HermGaussCond := Formalism.HermitianLatticeCounting.P.hermitian_gauss_condition
end Formalism.HermitianLatticeCounting.Final.S4
