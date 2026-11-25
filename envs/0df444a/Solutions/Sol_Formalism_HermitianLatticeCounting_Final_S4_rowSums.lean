-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.rowSums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:04.535556+00:00
-- url     : https://prove2.me/submissions/668bc25c-bbe1-4ae7-9876-b4a18e1d7f5b

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_matrix_line_sums
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_matrix_line_sums


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.RowSums := Formalism.HermitianLatticeCounting.P.matrix_line_sums
end Formalism.HermitianLatticeCounting.Final.S4
