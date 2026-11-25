-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.weightedCS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:03:42.063064+00:00
-- url     : https://prove2.me/submissions/a6debcf9-be3c-40ea-8282-35a3fbec2e3f

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_weighted_cauchy_schwarz
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_weighted_cauchy_schwarz


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.WeightedCS := Formalism.HermitianLatticeCounting.P.weighted_cauchy_schwarz
end Formalism.HermitianLatticeCounting.Final.S4
