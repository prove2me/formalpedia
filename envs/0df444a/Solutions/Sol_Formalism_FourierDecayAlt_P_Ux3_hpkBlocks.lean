-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.hpkBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:39:26.985551+00:00
-- url     : https://prove2.me/submissions/9c5e1e68-c396-4b5b-9479-555bacd55c0a

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_first_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_middle_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_last_val

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
theorem _root_.solution : HpkBlocks := by
  intro k j ρ
  ext i l
  rcases h : (eB k j ρ).symm i with ((a | a) | a) <;> rcases h' : (eB k j ρ).symm l with ((b | b) | b) <;>
    (rw [← (eB k j ρ).apply_symm_apply i, ← (eB k j ρ).apply_symm_apply l, h, h']) <;>
    (rw [block3_apply]; simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.zero_apply, G.wMat, Matrix.of_apply]
     unfold Hpk
     simp only [Fin.ext_iff, block_index_first_val, block_index_middle_val, block_index_last_val, Fin.val_rev]
     split_ifs <;> first | rfl | (exfalso; omega))
end Formalism.FourierDecayAlt.P.Ux3
