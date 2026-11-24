-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.block3_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:51.077017+00:00
-- url     : https://prove2.me/submissions/eb50b4cb-a451-41a3-a09f-5d215b265241

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
theorem _root_.solution : blk3 (k := k) (j := j) (ρ := ρ) 1 0 0 0 1 0 0 0 1 = 1 := by
  unfold blk3
  have h1 : Matrix.fromRows (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = 0 := by
    ext (a | a) b <;> rfl
  have h2 : Matrix.fromCols (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) = 0 := by
    ext a (b | b) <;> rfl
  rw [h1, h2, Matrix.fromBlocks_one, Matrix.fromBlocks_one]
  simp [Matrix.reindex_apply, Matrix.submatrix_one_equiv]
end Formalism.FourierDecayAlt.P.Ux3
