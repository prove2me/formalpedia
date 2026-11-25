-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.hermStdForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:00:38.161784+00:00
-- url     : https://prove2.me/submissions/f79aac7a-f2e1-4cb1-aad5-0f2ec6fb81fd

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hermitian_standard_form
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hermitian_standard_form


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.HermStdForm := Formalism.HermitianLatticeCounting.P.hermitian_standard_form
end Formalism.HermitianLatticeCounting.Final.S4
