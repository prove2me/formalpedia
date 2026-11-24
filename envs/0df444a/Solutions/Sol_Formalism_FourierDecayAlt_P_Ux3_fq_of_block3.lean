-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.fq_of_block3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:34.464811+00:00
-- url     : https://prove2.me/submissions/4e238a75-65d3-4429-a97f-51941fd7dda6

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul

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
theorem _root_.solution (Fj Fj' : Matrix (Fin (2 * ρ + k + 1)) (Fin (ρ + 1)) ℂ)
    (Q11 : Matrix (Fin j) (Fin j) ℂ) (Q12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (ColumnFamilies : Matrix (Fin j) (Fin j) ℂ)
    (Q21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (Q22 : B.Mat k ρ) (Q23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (Q31 : Matrix (Fin j) (Fin j) ℂ) (Q32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (Q33 : Matrix (Fin j) (Fin j) ℂ) :
    (Matrix.reindex (eB k j ρ) (eC j ρ) (F0 Fj))ᴴ * blk3 Q11 Q12 ColumnFamilies Q21 Q22 Q23 Q31 Q32 Q33 *
        Matrix.reindex (eB k j ρ) (eC j ρ) (F0 Fj') =
      Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks Q11 (Q12 * Fj') (Fjᴴ * Q21) (Fjᴴ * Q22 * Fj')) := by
  unfold blk3
  rw [Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  congr 1
  ext (a | a) (b | b) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, F0, Matrix.conjTranspose_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.one_apply]
end Formalism.FourierDecayAlt.P.Ux3
