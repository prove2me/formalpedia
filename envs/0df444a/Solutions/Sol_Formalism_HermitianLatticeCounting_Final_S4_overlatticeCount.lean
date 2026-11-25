-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.overlatticeCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:57:16.854461+00:00
-- url     : https://prove2.me/submissions/08b5f0ea-f208-40fe-9433-3443efb39df0

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_overlattice_count_formula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_overlattice_count_formula


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.OverlatticeCount := Formalism.HermitianLatticeCounting.P.overlattice_count_formula
end Formalism.HermitianLatticeCounting.Final.S4
