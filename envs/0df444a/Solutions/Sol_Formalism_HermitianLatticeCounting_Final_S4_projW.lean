-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.projW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:04:29.368458+00:00
-- url     : https://prove2.me/submissions/9f2d2333-704a-4825-b743-70429d3b48d9

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_projection_weight_formula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_projection_weight_formula


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.ProjW := Formalism.HermitianLatticeCounting.P.projection_weight_formula
end Formalism.HermitianLatticeCounting.Final.S4
