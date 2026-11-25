-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.superDiagAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:59:32.335076+00:00
-- url     : https://prove2.me/submissions/cb465195-ae0c-4025-92c4-9a2c0749d3aa

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_superdiagonal_addition_invariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_superdiagonal_addition_invariance


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.SuperDiagAdd := Formalism.HermitianLatticeCounting.P.superdiagonal_addition_invariance
end Formalism.HermitianLatticeCounting.Final.S4
