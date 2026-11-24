-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.relIndex_eq_ncard
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:38.112733+00:00
-- url     : https://prove2.me/submissions/cfcd2ea5-af53-4ee1-9b1f-e26fbf7c8a95

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

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
variable {G X : Type} [Group G] [MulAction G X]
open MulAction
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (K : Subgroup G) (z : X) :
    (stabilizer G z).relIndex K = (orbit K z).ncard := by
  rw [← index_stabilizer K z, Subgroup.relIndex]
  congr 1
end Formalism.HermitianLatticeCounting.P.S4aux
