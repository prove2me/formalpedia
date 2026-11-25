-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.unimodHull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:00:38.406255+00:00
-- url     : https://prove2.me/submissions/2e1e5fbd-17d8-4b1a-8fb4-fbd02f9e6418

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unimodular_hull
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_unimodular_hull


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.UnimodHull := Formalism.HermitianLatticeCounting.P.unimodular_hull
end Formalism.HermitianLatticeCounting.Final.S4
