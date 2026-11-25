-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.tauHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:59:38.915173+00:00
-- url     : https://prove2.me/submissions/b3c3e0cf-3d99-4966-bf6c-399298862215

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_involution_map_hom
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_involution_map_hom


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.TauHom := Formalism.HermitianLatticeCounting.P.involution_map_hom
end Formalism.HermitianLatticeCounting.Final.S4
