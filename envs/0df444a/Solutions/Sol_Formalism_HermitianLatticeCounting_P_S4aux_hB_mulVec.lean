-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hB_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:38.672842+00:00
-- url     : https://prove2.me/submissions/d7d1e6d5-1c0d-4aef-8938-bbfc1107a588

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
variable (K : Type) {L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {K}
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution {j : ℕ} (X : Fin j → Fin n → L) (x : Fin n → L) (b : Fin j) :
    hB K Ph x (X b) = (hMat K Ph X).mulVec x b := by
  simp only [hB, hMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
end Formalism.HermitianLatticeCounting.P.S4aux
