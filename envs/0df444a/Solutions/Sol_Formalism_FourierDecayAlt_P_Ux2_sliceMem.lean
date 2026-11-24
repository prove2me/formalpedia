-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.sliceMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:16:03.644578+00:00
-- url     : https://prove2.me/submissions/2dd8db34-ebc9-4bb1-acc0-d15f2f1c70fc

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_ct
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_hpkBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_sq_assoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution : SliceMem := by
  intro k j ρ
  refine ⟨?_, ?_, ?_⟩
  · intro Z γ hZ hγ
    have hγ' : γᴴ * Hpk k ρ * γ = Hpk k ρ := hγ
    have hZu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZ
    have hu : IsUnit Zᴴ.det := by
      rw [det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hZ)
    show (mMap k j ρ Z γ)ᴴ * Hpk k (j + ρ) * mMap k j ρ Z γ = Hpk k (j + ρ)
    rw [hpkBlocks k j ρ]; unfold mMap
    rw [block3_conjTranspose, block3_mul, block3_mul]
    refine block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [Matrix.mul_assoc, wMat_ct, Matrix.conjTranspose_nonsing_inv, wMat_sq_assoc, hγ', Matrix.nonsing_inv_mul _ hZu, Matrix.mul_nonsing_inv _ hu,
        Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hZu]
  · intro q hq
    have hqu : IsUnit q.det := isUnit_iff_ne_zero.mpr hq
    have hu : IsUnit qᴴ.det := by
      rw [det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hq)
    show (muP k j ρ q)ᴴ * Hpk k (j + ρ) * muP k j ρ q = Hpk k (j + ρ)
    rw [hpkBlocks k j ρ]; unfold muP
    rw [block3_conjTranspose, block3_mul, block3_mul]
    refine block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [Matrix.mul_assoc, wMat_ct, Matrix.conjTranspose_nonsing_inv, wMat_sq_assoc, Matrix.nonsing_inv_mul _ hqu, Matrix.mul_nonsing_inv _ hu,
        Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_left _ _ hqu]
  · intro y hy
    have hy' : yᴴ * Hpk k ρ * y = Hpk k ρ := hy
    show (embG k j ρ y)ᴴ * Hpk k (j + ρ) * embG k j ρ y = Hpk k (j + ρ)
    rw [hpkBlocks k j ρ]; unfold embG
    rw [block3_conjTranspose, block3_mul, block3_mul]
    refine block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [hy']
end Formalism.FourierDecayAlt.P.Ux2
