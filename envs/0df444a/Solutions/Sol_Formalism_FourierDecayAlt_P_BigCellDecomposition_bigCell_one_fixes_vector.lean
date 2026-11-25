-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellDecomposition.bigCell_one_fixes_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:04:07.162329+00:00
-- url     : https://prove2.me/submissions/fa1da4d1-7aa6-402c-ba36-9d4ab50ffc11

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellDecomposition
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.BigCellDecomposition
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) : bigCell k r c 1 *ᵥ z = z := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have key : ∀ j, bigCell k r c 1 i j * z j = if j = i then z i else 0 := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
      split_ifs with h
      · subst h
        exact (hz _ hj).symm
      · rfl
    · have hj1 : ¬ j.val < r := by omega
      have hj2 : j.val ≤ r + k := by omega
      simp only [bigCell, dif_neg hj1, dif_pos hj2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · simp only [dif_pos hi, Matrix.one_apply]
        by_cases hij : j = i
        · subst hij
          simp
        · have hne : (⟨i.val - r, by omega⟩ : Fin (k + 1)) ≠ ⟨j.val - r, by omega⟩ := by
            intro h
            apply hij
            ext
            simp only [Fin.mk.injEq] at h
            omega
          simp [hne, hij]
      · simp only [dif_neg hi, zero_mul]
        rw [if_neg]
        rintro rfl
        omega
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp
end Formalism.FourierDecayAlt.P.BigCellDecomposition
