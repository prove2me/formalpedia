-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.tuple_jacobian_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:11.313049+00:00
-- url     : https://prove2.me/submissions/c617d933-9f4d-4633-a3d3-ff999978edba

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
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
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : TupleJac := by
  intro E _ n m A
  have := LinearMap.det_pi (R := E) (ι := Fin n) (M := Fin m → E) (fun _ => Matrix.vecMulLinear A)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  have hA : LinearMap.det (Matrix.vecMulLinear A) = A.det := by
    rw [← Matrix.det_transpose A, ← LinearMap.det_toLin' A.transpose]
    congr 1
    ext v i
    simp [Matrix.vecMulLinear, Matrix.toLin'_apply]
  rw [hA] at this
  rw [← this]
  rfl
end Formalism.HermitianLatticeCounting.P.S4aux
