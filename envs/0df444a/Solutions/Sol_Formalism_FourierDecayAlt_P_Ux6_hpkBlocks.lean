-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.hpkBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:53:54.27048+00:00
-- url     : https://prove2.me/submissions/0054ebde-ff86-4475-98a1-daabebe171eb

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block_index_first_val_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block_index_middle_val_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block_index_last_val_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_ext_eB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution : HpkBlocks := by
  intro k j ρ
  apply ext_eB
  rintro (((a | a) | a)) (((b | b) | b)) <;>
    simp only [block3_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, G.wMat, Matrix.of_apply, Hpk, Fin.ext_iff, block_index_first_val_eq, block_index_middle_val_eq, block_index_last_val_eq,
      Fin.val_rev] <;>
    split_ifs <;> first | rfl | omega
end Formalism.FourierDecayAlt.P.Ux6
