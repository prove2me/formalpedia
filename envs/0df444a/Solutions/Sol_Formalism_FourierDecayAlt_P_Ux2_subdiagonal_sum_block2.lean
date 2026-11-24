-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.subdiagonal_sum_block2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:55:15.710439+00:00
-- url     : https://prove2.me/submissions/f64b5026-161b-48e5-8f6b-4f23867ee991

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block2_apply_upper_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block2_apply_lower_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block2_apply_lower_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p s : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) :
    subS (blk2 A B C D) = subS A + (if h : 0 < s ∧ 0 < p then C ⟨0, h.1⟩ ⟨p - 1, by omega⟩ else 0) + subS D := by
  unfold subS
  rw [Fin.sum_univ_add]
  have h1 : ∀ i : Fin p, (if h : (Fin.castAdd s i).val + 1 < p + s then blk2 A B C D ⟨(Fin.castAdd s i).val + 1, h⟩ (Fin.castAdd s i) else 0) =
      (if h : i.val + 1 < p then A ⟨i.val + 1, h⟩ i else 0) +
        (if h : i.val + 1 = p ∧ 0 < s then C ⟨0, h.2⟩ i else 0) := by
    intro i
    have hi := i.isLt
    by_cases ha : i.val + 1 < p
    · have hlt : (Fin.castAdd s i).val + 1 < p + s := by simp; omega
      rw [dif_pos hlt, dif_pos ha, dif_neg (by omega), add_zero]
      have e : (⟨(Fin.castAdd s i).val + 1, hlt⟩ : Fin (p + s)) = Fin.castAdd s ⟨i.val + 1, ha⟩ := Fin.ext (by simp)
      rw [e, block2_apply_upper_left]
    · by_cases hs : 0 < s
      · have hlt : (Fin.castAdd s i).val + 1 < p + s := by simp; omega
        rw [dif_pos hlt, dif_neg ha, dif_pos ⟨by omega, hs⟩, zero_add]
        have e : (⟨(Fin.castAdd s i).val + 1, hlt⟩ : Fin (p + s)) = Fin.natAdd p ⟨0, hs⟩ := Fin.ext (by simp; omega)
        rw [e, block2_apply_lower_left]
      · rw [dif_neg (by simp; omega), dif_neg ha, dif_neg (by omega), add_zero]
  have h2 : ∀ i : Fin s, (if h : (Fin.natAdd p i).val + 1 < p + s then blk2 A B C D ⟨(Fin.natAdd p i).val + 1, h⟩ (Fin.natAdd p i) else 0) =
      (if h : i.val + 1 < s then D ⟨i.val + 1, h⟩ i else 0) := by
    intro i
    by_cases ha : i.val + 1 < s
    · have hlt : (Fin.natAdd p i).val + 1 < p + s := by simp; omega
      rw [dif_pos hlt, dif_pos ha]
      have e : (⟨(Fin.natAdd p i).val + 1, hlt⟩ : Fin (p + s)) = Fin.natAdd p ⟨i.val + 1, ha⟩ := Fin.ext (by simp; omega)
      rw [e, block2_apply_lower_right]
    · rw [dif_neg (by simp; omega), dif_neg ha]
  simp only [h1, h2, Finset.sum_add_distrib]
  congr 2
  by_cases hps : 0 < s ∧ 0 < p
  · rw [dif_pos hps, Finset.sum_eq_single ⟨p - 1, by omega⟩]
    · rw [dif_pos ⟨by simp; omega, hps.1⟩]
    · intro i _ hi
      rw [dif_neg]
      rintro ⟨h, -⟩
      exact hi (Fin.ext (by simp; omega))
    · simp
  · rw [dif_neg hps]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [dif_neg]
    rintro ⟨h, h'⟩
    exact hps ⟨h', by omega⟩
end Formalism.FourierDecayAlt.P.Ux2
