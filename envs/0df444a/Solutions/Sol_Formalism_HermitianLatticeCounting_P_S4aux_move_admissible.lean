-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.move_admissible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:16.221659+00:00
-- url     : https://prove2.me/submissions/492ee2d0-00aa-4086-819f-6f2e8cbeba68

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_move_congruence
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_moveAdm
import Theorems.Thm_Formalism_SL_Final_eichInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : MoveAdm := Part2.moveAdm move_congruence Formalism.SL.Final.eichInv
end Formalism.HermitianLatticeCounting.P.S4aux
