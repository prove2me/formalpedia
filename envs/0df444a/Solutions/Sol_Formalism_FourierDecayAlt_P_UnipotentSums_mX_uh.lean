-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.mX_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:35:03.363179+00:00
-- url     : https://prove2.me/submissions/bbeee394-ecbf-4f2b-af7e-4f64cd70531b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_sum_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_sig_eI
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_sig_esI
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_sum_Xs
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_sgn_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_apply_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_apply_Xs
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_unipotent_apply_middle_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_col_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_unipotent_apply_middle_column
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_col_Xs
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_Hpk_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_sig_fixes_middle_block


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentSums
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.UnipotentSums
theorem _root_.solution (vX : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit vX.det) : C2.mX k r vX ∈ UH (Hpk k r) := by
  have hu' : IsUnit vXᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
  have hs1 : ∀ c : Fin r, GBasic.sgn k r (eI k r c) = 1 := fun c => sgn_X _ (Or.inl c.isLt)
  have hs2 : ∀ c : Fin r, GBasic.sgn k r (esI k r c) = 1 := fun c =>
    sgn_X _ (Or.inr (by have := c.isLt; show r + k < 2 * r + k - c.val; omega))
  show (C2.mX k r vX)ᴴ * Hpk k r * C2.mX k r vX = Hpk k r
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Hpk_mul_apply, Matrix.conjTranspose_apply]
  have hilt := i.isLt
  have hjlt := j.isLt
  by_cases hi1 : i.val < r
  · obtain ⟨a, rfl⟩ : ∃ a : Fin r, eI k r a = i := ⟨⟨i.val, hi1⟩, Fin.ext rfl⟩
    have ha := a.isLt
    have hea : (eI k r a).val = a.val := rfl
    rw [sum_X _ (fun p hp => by
      rw [mX_col_X, dif_neg (show ¬ p.val < r by omega), star_zero, zero_mul])]
    have hcol : ∀ c : Fin r, C2.mX k r vX (eI k r c) (eI k r a) = vX c a := fun c => by
      rw [mX_col_X, dif_pos (show (eI k r c).val < r from c.isLt)]
      rfl
    simp only [sig_eI, hs1, one_mul, hcol, mX_apply_Xs]
    by_cases hj : r + k < j.val
    · simp only [dif_pos hj]
      have key : ∑ c : Fin r, star (vX c a) * (vXᴴ)⁻¹ c ⟨2 * r + k - j.val, by omega⟩ =
          (vXᴴ * (vXᴴ)⁻¹) a ⟨2 * r + k - j.val, by omega⟩ := by
        rw [Matrix.mul_apply]
        simp only [Matrix.conjTranspose_apply]
      rw [key, Matrix.mul_nonsing_inv _ hu', Matrix.one_apply]
      simp only [Hpk, Fin.ext_iff]
      show _ = if a.val < r ∧ a.val + j.val = 2 * r + k then (1 : ℂ) else _
      split_ifs <;> first | rfl | (exfalso; omega) | omega
    · simp only [dif_neg hj, mul_zero, Finset.sum_const_zero]
      simp only [Hpk]
      show (0 : ℂ) = if a.val < r ∧ a.val + j.val = 2 * r + k then (1 : ℂ) else _
      split_ifs <;> first | rfl | (exfalso; omega) | omega
  · by_cases hi2 : r + k < i.val
    · obtain ⟨a, rfl⟩ : ∃ a : Fin r, esI k r a = i :=
        ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)⟩
      have ha := a.isLt
      have hea : (esI k r a).val = 2 * r + k - a.val := rfl
      rw [sum_Xs _ (fun p hp => by
        rw [mX_col_Xs, dif_neg (show ¬ r + k < p.val by omega), star_zero, zero_mul])]
      have hcol : ∀ c : Fin r, C2.mX k r vX (esI k r c) (esI k r a) = (vXᴴ)⁻¹ c a := fun c => by
        have hc := c.isLt
        rw [mX_col_Xs, dif_pos (show r + k < (esI k r c).val from by show r + k < 2 * r + k - c.val; omega)]
        have e : (⟨2 * r + k - (esI k r c).val, by show 2 * r + k - (2 * r + k - c.val) < r; omega⟩ : Fin r) = c :=
          Fin.ext (by show 2 * r + k - (2 * r + k - c.val) = c.val; omega)
        rw [e]
      simp only [sig_esI, hs2, one_mul, hcol, mX_apply_X]
      by_cases hj : j.val < r
      · simp only [dif_pos hj]
        have key : ∑ c : Fin r, star ((vXᴴ)⁻¹ c a) * vX c ⟨j.val, hj⟩ =
            (((vXᴴ)⁻¹)ᴴ * vX) a ⟨j.val, hj⟩ := by
          rw [Matrix.mul_apply]
          simp only [Matrix.conjTranspose_apply]
        rw [key, ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose,
          Matrix.nonsing_inv_mul _ hu, Matrix.one_apply]
        simp only [Hpk, Fin.ext_iff]
        show _ = if 2 * r + k - a.val < r ∧ 2 * r + k - a.val + j.val = 2 * r + k then (1 : ℂ) else _
        split_ifs <;> first | rfl | (exfalso; omega) | omega
      · simp only [dif_neg hj, mul_zero, Finset.sum_const_zero]
        simp only [Hpk]
        show (0 : ℂ) = if 2 * r + k - a.val < r ∧ 2 * r + k - a.val + j.val = 2 * r + k then (1 : ℂ) else _
        split_ifs <;> first | rfl | (exfalso; omega) | omega
    · rw [Finset.sum_eq_single i (fun p _ hp => by
          rw [unipotent_apply_middle_column vX p i (by omega) (by omega), if_neg hp, star_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ i) h)]
      rw [unipotent_apply_middle_column vX i i (by omega) (by omega), if_pos rfl, star_one, one_mul,
        FlagSpanVanishing.sig_fixes_middle_block i ⟨by omega, by omega⟩, unipotent_apply_middle_row vX i j (by omega) (by omega)]
      simp only [GBasic.sgn, Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega) | omega | simp
end Formalism.FourierDecayAlt.P.UnipotentSums
