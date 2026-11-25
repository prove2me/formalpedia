-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.spanCharRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:03:37.671519+00:00
-- url     : https://prove2.me/submissions/54a3fd8f-6398-4a24-89a4-661bdff2a19f

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_span_character_ring
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_span_character_ring


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.SpanCharRing := Formalism.HermitianLatticeCounting.P.span_character_ring
end Formalism.HermitianLatticeCounting.Final.S4
