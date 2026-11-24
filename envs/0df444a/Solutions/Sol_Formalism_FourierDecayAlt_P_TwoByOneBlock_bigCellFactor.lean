-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.bigCellFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:05.79289+00:00
-- url     : https://prove2.me/submissions/f2702684-82ac-4813-89df-9b9e50cbe061

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_bc_mid_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_bc_mid_row_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_bc_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_bc_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_bc_one_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_out_row


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution : BigCellFactor := by
  intro k r c μ
  constructor
  · ext i j
    rw [Matrix.mul_apply]
    by_cases hj : mid k r j
    · by_cases hi : mid k r i
      · rw [Finset.sum_eq_single i]
        · rw [bc_one_mid c i i hi hi, if_pos rfl, one_mul, emb_mid μ i j hi hj, bc_mid_col c μ i j hj, dif_pos hi]
        · intro q _ hq
          by_cases hqm : mid k r q
          · rw [bc_one_mid c i q hi hqm, if_neg (fun h => hq h.symm), zero_mul]
          · rw [bc_mid_row_out c 1 i q hi hqm, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [bc_mid_col c μ i j hj, dif_neg hi]
        symm
        apply Finset.sum_eq_zero
        intro q _
        by_cases hqm : mid k r q
        · rw [bc_mid_col c 1 i q hqm, dif_neg hi, zero_mul]
        · rw [emb_out_row μ q j hqm, if_neg (show ¬ (q = j) from fun h => hqm (h ▸ hj)), mul_zero]
    · rw [Finset.sum_eq_single j]
      · rw [emb_out_col μ j j hj, if_pos rfl, mul_one]
        exact bc_out_col c μ 1 i j hj
      · intro q _ hq
        rw [emb_out_col μ q j hj, if_neg hq, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  · ext i j
    rw [Matrix.mul_apply]
    by_cases hi : mid k r i
    · by_cases hj : mid k r j
      · rw [Finset.sum_eq_single j]
        · rw [bc_one_mid c j j hj hj, if_pos rfl, mul_one, emb_mid μ i j hi hj, bc_mid_col c μ i j hj, dif_pos hi]
        · intro q _ hq
          by_cases hqm : mid k r q
          · rw [bc_one_mid c q j hqm hj, if_neg hq, mul_zero]
          · rw [emb_out_col μ i q hqm, if_neg (show ¬ (i = q) from fun h => hqm (h ▸ hi)), zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [bc_mid_row_out c μ i j hi hj]
        symm
        apply Finset.sum_eq_zero
        intro q _
        by_cases hqm : mid k r q
        · rw [bc_mid_row_out c 1 q j hqm hj, mul_zero]
        · rw [emb_out_col μ i q hqm, if_neg (show ¬ (i = q) from fun h => hqm (h ▸ hi)), zero_mul]
    · rw [Finset.sum_eq_single i]
      · rw [emb_out_row μ i i hi, if_pos rfl, one_mul]
        exact bc_out_row c μ 1 i j hi
      · intro q _ hq
        rw [emb_out_row μ i q hi, if_neg (fun h => hq h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.TwoByOneBlock
