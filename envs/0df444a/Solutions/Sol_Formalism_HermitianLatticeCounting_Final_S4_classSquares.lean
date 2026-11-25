-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.classSquares
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:14:52.089257+00:00
-- url     : https://prove2.me/submissions/5bc9f97e-63f6-4bd7-a885-e79e47959a74

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_class_number_squares
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_class_number_squares


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.ClassSquares := Formalism.HermitianLatticeCounting.P.class_number_squares
end Formalism.HermitianLatticeCounting.Final.S4
