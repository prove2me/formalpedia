-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.t_bigcellfactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:52:39.538795+00:00
-- url     : https://prove2.me/submissions/3d87d690-00b0-4195-91e7-a8a64cfbf062

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_emb_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_bc_mid_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_bc_mid_row_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_bc_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_bc_one_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_row


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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution : BigCellFactor := by
  intro k r c μ
  constructor
  · ext i j
    rw [Matrix.mul_apply]
    by_cases hj : midW k r j
    · rw [Finset.sum_eq_single i]
      · by_cases hi : midW k r i
        · rw [bc_one_mid c i i hi hi, if_pos (rfl : i = i), one_mul, emb_mid μ i j hi hj, bc_mid_col c μ i j hj,
            dif_pos hi]
        · rw [emb_out_row μ i j hi, if_neg (fun h => by subst h; exact hi hj), mul_zero, bc_mid_col c μ i j hj,
            dif_neg hi]
      · intro m _ hm
        by_cases hm' : midW k r m
        · by_cases hi : midW k r i
          · rw [bc_one_mid c i m hi hm', if_neg (Ne.symm hm), zero_mul]
          · rw [bc_mid_col c 1 i m hm', dif_neg hi, zero_mul]
        · rw [emb_out_row μ m j hm', if_neg (fun h => by subst h; exact hm' hj), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single j]
      · rw [emb_out_col μ j j hj, if_pos (rfl : j = j), mul_one, bc_out_col c 1 μ i j hj]
      · intro m _ hm
        rw [emb_out_col μ m j hj, if_neg hm, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
  · ext i j
    rw [Matrix.mul_apply]
    by_cases hj : midW k r j
    · rw [Finset.sum_eq_single j]
      · rw [bc_one_mid c j j hj hj, if_pos (rfl : j = j), mul_one, bc_mid_col c μ i j hj]
        by_cases hi : midW k r i
        · rw [emb_mid μ i j hi hj, dif_pos hi]
        · rw [emb_out_row μ i j hi, dif_neg hi, if_neg (fun h => by subst h; exact hi hj)]
      · intro m _ hm
        by_cases hm' : midW k r m
        · rw [bc_one_mid c m j hm' hj, if_neg hm, mul_zero]
        · rw [bc_mid_col c 1 m j hj, dif_neg hm', mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single i]
      · by_cases hi : midW k r i
        · rw [bc_mid_row_out c 1 i j hi hj, mul_zero, bc_mid_row_out c μ i j hi hj]
        · rw [emb_out_col μ i i hi, if_pos (rfl : i = i), one_mul, bc_out_col c 1 μ i j hj]
      · intro m _ hm
        by_cases hm' : midW k r m
        · rw [bc_mid_row_out c 1 m j hm' hj, mul_zero]
        · rw [emb_out_col μ i m hm', if_neg (Ne.symm hm), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.LongWeylElement
