-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hB_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:30.691318+00:00
-- url     : https://prove2.me/submissions/5aa9a606-032c-4894-abcf-9b3707456dda

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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (c : L) (x y : Fin n → L) :
    hB K Ph x (c • y) = c ^ Fintype.card K * hB K Ph x y := by
  simp only [hB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_pow]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
end Formalism.HermitianLatticeCounting.P.S4aux
