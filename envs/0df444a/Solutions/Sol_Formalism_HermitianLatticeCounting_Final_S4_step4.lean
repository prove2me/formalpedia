-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.step4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:23.546491+00:00
-- url     : https://prove2.me/submissions/961a9b74-7ab0-4f0f-bb36-8d26fa1c03dd

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_fourth_reduction_identity
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_fourth_reduction_identity


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.Step4 := Formalism.HermitianLatticeCounting.P.fourth_reduction_identity
end Formalism.HermitianLatticeCounting.Final.S4
