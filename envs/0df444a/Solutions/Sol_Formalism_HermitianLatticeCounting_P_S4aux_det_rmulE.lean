-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.det_rmulE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:34:29.805269+00:00
-- url     : https://prove2.me/submissions/0ef91eff-85a5-4954-9139-a1eac8085904

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_tuple_jacobian_alt

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
variable {E : Type} [CommRing E]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (m : ℕ) (A : Matrix (Fin m) (Fin m) E) : LinearMap.det (rmulE m A) = A.det ^ m :=
  tuple_jacobian_alt E m m A
end Formalism.HermitianLatticeCounting.P.S4aux
