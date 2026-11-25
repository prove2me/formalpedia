-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S4.bridgeSelfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:08:08.233706+00:00
-- url     : https://prove2.me/submissions/80f0d7fc-a81e-4c78-aecf-b7456e4e2d20

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_ValuationProductBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_self_dual_lattice_extension
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_self_dual_lattice_extension


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S4.BridgeSelfDual := Formalism.HermitianLatticeCounting.P.self_dual_lattice_extension
end Formalism.HermitianLatticeCounting.Final.S4
