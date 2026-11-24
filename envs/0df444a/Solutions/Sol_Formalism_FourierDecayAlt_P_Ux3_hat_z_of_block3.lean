-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.hat_z_of_block3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:25:59.536629+00:00
-- url     : https://prove2.me/submissions/6d80a15b-4ca6-4783-97bb-a12a34a76f4a

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_first_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_last_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ) :
    Zh k j ρ (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) = G.wMat j * A31 := by
  ext a b
  rw [wMat_mul_apply]
  have h1 : (⟨2 * (j + ρ) + k - a.val, by omega⟩ : Fin (2 * (j + ρ) + k + 1)) = eB k j ρ (Sum.inr a.rev) := by
    apply Fin.ext
    rw [block_index_last_val]
    simp only [Fin.val_rev]
    omega
  have h2 : (⟨b.val, by omega⟩ : Fin (2 * (j + ρ) + k + 1)) = eB k j ρ (Sum.inl (Sum.inl b)) := by
    apply Fin.ext
    rw [block_index_first_val]
  simp only [Zh]
  rw [h1, h2, block3_apply]
  simp
end Formalism.FourierDecayAlt.P.Ux3
