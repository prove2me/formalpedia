-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.hermJac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:00:29.215304+00:00
-- url     : https://prove2.me/submissions/a3f7aec1-216a-4ce1-9cab-165412af95f7

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hermitian_jacobian
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hermitian_jacobian


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.HermJac := Formalism.HermitianLatticeCounting.P.hermitian_jacobian
end Formalism.HermitianLatticeCounting.Final.S4
