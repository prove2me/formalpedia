-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.leakAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:01:44.24126+00:00
-- url     : https://prove2.me/submissions/5c67765f-9e5f-48ed-b956-93b4ec39b2ad

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_leakage_algebraic_identity
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_leakage_algebraic_identity


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.LeakAlg := Formalism.HermitianLatticeCounting.P.leakage_algebraic_identity
end Formalism.HermitianLatticeCounting.Final.S4
