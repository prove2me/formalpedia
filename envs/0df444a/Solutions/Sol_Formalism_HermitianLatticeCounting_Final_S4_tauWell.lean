-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.tauWell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:00:02.143228+00:00
-- url     : https://prove2.me/submissions/f86bfecd-fec1-4678-a63c-0a641a1c8df2

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_involution_well_defined
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_involution_well_defined


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.TauWell := Formalism.HermitianLatticeCounting.P.involution_well_defined
end Formalism.HermitianLatticeCounting.Final.S4
