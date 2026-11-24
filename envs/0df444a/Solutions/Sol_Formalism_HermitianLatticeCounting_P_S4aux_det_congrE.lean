-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.det_congrE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:22.334537+00:00
-- url     : https://prove2.me/submissions/1678a23a-9ac4-49ad-b7f2-97d4d2ea5c25

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_rmulE
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_lmulE

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
theorem _root_.solution [StarRing E] (m : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (rmulE m A ∘ₗ lmulE m A.conjTranspose) = (A.det * star A.det) ^ m := by
  rw [LinearMap.det_comp, det_rmulE, det_lmulE, Matrix.det_conjTranspose, mul_pow]
end Formalism.HermitianLatticeCounting.P.S4aux
