-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.zb_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:59:51.571221+00:00
-- url     : https://prove2.me/submissions/bb34ae99-8636-4d92-b27f-967f85e623da

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SignPermutationIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_succAbove_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3
private theorem sgnW_succ' (s : ℕ) : sgnW (s + 1) = (-1) ^ s * sgnW s := by
  unfold sgnW
  rw [← pow_add]
  congr 1
  cases s with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring
end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (i0 s : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) :
    (Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val).det = h.det * t ^ s * sgnW s := by
  induction s with
  | zero =>
    have hs : sgnW 0 = 1 := by simp [sgnW]
    rw [hs, pow_zero, mul_one, mul_one]
    show Matrix.det (Matrix.of fun a b : Fin i0 => Zb i0 0 h t a.val b.val) = _
    congr 1
    ext a b
    simp [Zb, a.isLt, b.isLt]
  | succ s ih =>
    rw [Matrix.det_succ_row _ (⟨i0, by omega⟩ : Fin (i0 + s + 1)), Finset.sum_eq_single (Fin.last _)]
    · have hsub : (Matrix.of fun a b : Fin (i0 + (s + 1)) => Zb i0 (s + 1) h t a.val b.val).submatrix
          (⟨i0, by omega⟩ : Fin (i0 + s + 1)).succAbove (Fin.last (i0 + s)).succAbove =
          Matrix.of fun a b : Fin (i0 + s) => Zb i0 s h t a.val b.val := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, succAbove_val, Fin.succAbove_last,
          Fin.coe_castSucc]
        have hb := b.isLt
        by_cases ha : (a : ℕ) < i0
        · simp only [ha, if_true]
          unfold Zb
          split_ifs <;> first | rfl | omega
        · simp only [ha, if_false]
          unfold Zb
          split_ifs <;> first | rfl | omega
      rw [hsub, ih, sgnW_succ']
      have he : Zb i0 (s + 1) h t i0 (i0 + s) = t := by
        simp only [Zb]
        rw [dif_neg (lt_irrefl _), if_pos (by omega)]
      simp only [Matrix.of_apply, Fin.val_last]
      rw [he]
      rw [show i0 + (i0 + s) = 2 * i0 + s by ring, pow_add, pow_mul]
      norm_num
      ring
    · intro j _ hj
      have hj' : (j : ℕ) ≠ i0 + s := fun e => hj (Fin.ext (by simp [e]))
      have he : Zb i0 (s + 1) h t i0 j = 0 := by
        have := j.isLt
        simp only [Zb]
        rw [dif_neg (lt_irrefl _), if_neg (by omega)]
      simp only [Matrix.of_apply]
      rw [he, mul_zero, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
end Formalism.FourierDecayAlt.P.SignAntidiagonal
