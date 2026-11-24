-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hMat_li
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:30.983036+00:00
-- url     : https://prove2.me/submissions/af039a01-3955-4a41-803b-2d57b81a706d

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_frob_sum
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
theorem _root_.solution (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det) {j : ℕ} (X : Fin j → Fin n → L)
    (hX : LinearIndependent L X) : LinearIndependent L (hMat K Ph X).row := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set w : Fin n → L := fun l => ∑ b, g b * X b l ^ Fintype.card K with hw
  have h1 : Ph.mulVec w = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.row, hMat, Matrix.of_apply, smul_eq_mul,
      Pi.zero_apply, Finset.mul_sum] at this
    simp only [Matrix.mulVec, dotProduct, hw, Finset.mul_sum, Pi.zero_apply]
    rw [Finset.sum_comm, ← this]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => by ring
  have h3 : w = 0 := by
    have : Ph⁻¹.mulVec (Ph.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Ph hPh, Matrix.one_mulVec]
    rw [← this, h1, Matrix.mulVec_zero]
  have h4 : ∑ b, (g b ^ Fintype.card K) • X b = 0 := by
    funext l
    have := congrArg (fun z => z ^ Fintype.card K) (congrFun h3 l)
    simp only [hw, frob_sum, mul_pow, frob_frob h2, Pi.zero_apply] at this
    rw [zero_pow Fintype.card_pos.ne'] at this
    simpa [Finset.sum_apply] using this
  intro b
  have := (Fintype.linearIndependent_iff.1 hX) _ h4 b
  exact pow_eq_zero_iff (Fintype.card_pos.ne') |>.1 this
end Formalism.HermitianLatticeCounting.P.S4aux
