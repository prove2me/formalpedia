-- Prove2me | solution 1 for Formalism.L2.Pj.iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:35:26.362314+00:00
-- url     : https://prove2.me/submissions/f3b55f9f-15fc-432f-b7d7-226e5b135cb8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Theorems.Thm_Formalism_L2_Pj_exists_clear_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open Matrix IsDedekindDomain
variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]
namespace Formalism.L2.Pj
theorem _root_.solution : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
    ∃ (k : Matrix (Fin n) (Fin n) V) (U : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ U.BlockTriangular id ∧
      (∀ i, U i i ≠ 0) ∧ A = k.map (algebraMap V F) * U
  | 0, A, _ => ⟨1, A, by simp, fun i => i.elim0, fun i => i.elim0, by ext i; exact i.elim0⟩
  | n + 1, A, hA => by
    obtain ⟨Q, hQ, hQA⟩ := exists_clear_col (V := V) A hA
    set B := Q.map (algebraMap V F) * A with hB
    have hdetB : B.det = B 0 0 * (B.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [hQA, B]
    have hQF : (Q.map (algebraMap V F)).det = algebraMap V F Q.det := by
      rw [RingHom.map_det]; rfl
    have hBne : B.det ≠ 0 := by
      rw [hB, Matrix.det_mul, hQF]
      exact mul_ne_zero (hQ.map (algebraMap V F)).ne_zero hA
    have hB00 : B 0 0 ≠ 0 := by intro h; apply hBne; rw [hdetB, h, zero_mul]
    obtain ⟨k', U', hk', hU', hd', hA'⟩ := solution (B.submatrix Fin.succ Fin.succ) (by
      intro h; apply hBne; rw [hdetB, h, mul_zero])
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => k' i' j') j) i
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j =>
      Fin.cases (B 0 j) (fun i' => Fin.cases 0 (fun j' => U' i' j') j) i
    have hKU : K.map (algebraMap V F) * U = B := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ, hQA]
        · have h1 := congrFun (congrFun hA' i') j'
          simp only [Matrix.submatrix_apply] at h1
          rw [h1]
          simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
    have hKdet : K.det = k'.det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [K]
      rfl
    refine ⟨Q⁻¹ * K, U, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, hKdet]
      exact (Matrix.isUnit_nonsing_inv_det Q hQ).mul hk'
    · intro i j hij
      induction i using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp [U]
        | succ j' =>
          have : j' < i' := Fin.succ_lt_succ_iff.1 hij
          simpa [U] using hU' this
    · intro i
      induction i using Fin.cases with
      | zero => simpa [U] using hB00
      | succ i' => simpa [U] using hd' i'
    · rw [Matrix.map_mul, Matrix.mul_assoc, hKU, hB, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul Q hQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
end Formalism.L2.Pj
