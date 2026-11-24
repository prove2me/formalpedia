-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.minor_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:51.247286+00:00
-- url     : https://prove2.me/submissions/01fbb20d-7bc1-4be3-9f46-ce6143896348

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_eC_symm_castAdd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_eC_symm_natAdd

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
theorem _root_.solution (Z : Matrix (Fin j) (Fin j) ℂ) (W : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ) (l : ℕ)
    (hl : l ≤ ρ + 1) (h : j + l ≤ j + ρ + 1) :
    ((Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks Z 0 0 W)).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      Z.det * (W.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have e : (Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks Z 0 0 W)).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks Z 0 0 (W.submatrix (Fin.castLE hl) (Fin.castLE hl))) := by
    ext a b
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
      simp [Matrix.reindex_apply, eC_symm_castAdd h, eC_symm_natAdd h hl]
  rw [e, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
end Formalism.FourierDecayAlt.P.Ux3
