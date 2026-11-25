-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.kernelAvgSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:08:18.98496+00:00
-- url     : https://prove2.me/submissions/daaab39f-2529-41c3-96eb-3da42886b0ca

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_kernel_average_sum
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_kernel_average_sum


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.KernelAvgSum := Formalism.HermitianLatticeCounting.P.kernel_average_sum
end Formalism.HermitianLatticeCounting.Final.S4
