-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.primDensitySplitForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:02:00.328551+00:00
-- url     : https://prove2.me/submissions/bb6dbbe4-4067-4720-bf31-fe7bf4f09aab

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_primitive_density_split_form
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_primitive_density_split_form


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.PrimDensitySplitForm := Formalism.HermitianLatticeCounting.P.primitive_density_split_form
end Formalism.HermitianLatticeCounting.Final.S4
