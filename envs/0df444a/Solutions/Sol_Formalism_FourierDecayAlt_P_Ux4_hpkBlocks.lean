-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.hpkBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:48:33.368019+00:00
-- url     : https://prove2.me/submissions/797658d6-0ef8-4e0f-a682-0fecb8afe318

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block_index_first_val_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block_index_middle_val_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block_index_last_val_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_ext_eB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution : HpkBlocks := by
  intro k j ρ
  apply ext_eB
  intro x y
  rw [block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;>
  · have ha := a.isLt
    have hb := b.isLt
    simp only [Hpk, G.wMat, Fin.ext_iff, block_index_first_val_eq, block_index_middle_val_eq, block_index_last_val_eq, Fin.val_rev, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.zero_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
end Formalism.FourierDecayAlt.P.Ux4
