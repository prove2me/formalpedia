-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.primDensityInertForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:45.401547+00:00
-- url     : https://prove2.me/submissions/89047d90-0a1a-4594-9e83-2aa00f5c0109

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_primitive_density_inert_form
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_primitive_density_inert_form


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.PrimDensityInertForm := Formalism.HermitianLatticeCounting.P.primitive_density_inert_form
end Formalism.HermitianLatticeCounting.Final.S4
