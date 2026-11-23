-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.det_lmulE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:45.855566+00:00
-- url     : https://prove2.me/submissions/48f5b42a-7500-433a-b849-6adc84ef56d7

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_rmulE
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {E : Type} [CommRing E]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (m : ℕ) (B : Matrix (Fin m) (Fin m) E) : LinearMap.det (lmulE m B) = B.det ^ m := by
  have h1 : lmulE m B = ((Matrix.transposeLinearEquiv (Fin m) (Fin m) E E : _ ≃ₗ[E] _) : _ →ₗ[E] _) ∘ₗ
      rmulE m B.transpose ∘ₗ
      ((Matrix.transposeLinearEquiv (Fin m) (Fin m) E E).symm : _ →ₗ[E] _) := by
    ext X i j
    simp only [lmulE, rmulE, Matrix.transposeLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    change (B * X) i j = (X.transpose * B.transpose).transpose i j
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  rw [h1, LinearMap.det_conj, det_rmulE, Matrix.det_transpose]
end Formalism.HermitianLatticeCounting.P.S4aux
