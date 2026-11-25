-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.detKills
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:57:26.351836+00:00
-- url     : https://prove2.me/submissions/a069e6a2-7169-41cf-a63e-e0bff5942707

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_determinant_annihilates
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_determinant_annihilates


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.DetKills := Formalism.HermitianLatticeCounting.P.determinant_annihilates
end Formalism.HermitianLatticeCounting.Final.S4
