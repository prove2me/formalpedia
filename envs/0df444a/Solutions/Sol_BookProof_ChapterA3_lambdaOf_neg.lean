-- Prove2me | solution 1 for BookProof.ChapterA3.lambdaOf_neg
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:56:09.558964+00:00
-- url     : https://prove2.me/submissions/85a1bd64-e0f1-4b5c-b13f-97572bd53943

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix
set_option autoImplicit false
set_option maxHeartbeats 0

private lemma indep_local (c : Fin 4 → ℝ)
    (h : ∑ ν, c ν • mgammaR ν = 0) : ∀ ν, c ν = 0 := by
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) h
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) h
  have h20 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 0) h
  norm_num [mgammaR, mgammaZ, Fin.sum_univ_four, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h00 h01 h02 h20
  have h0 : c 0 = 0 := by linarith
  have h2 : c 2 = 0 := by linarith
  intro ν
  fin_cases ν
  · exact h0
  · exact h00
  · exact h2
  · exact h01

private lemma unique_local {S A B : Matrix (Fin 4) (Fin 4) ℝ}
    (ha : HasLambda S A) (hb : HasLambda S B) : A = B := by
  ext μ ν
  have hz : ∑ k, (A μ k - B μ k) • mgammaR k = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib]
    rw [← ha μ, ← hb μ, sub_self]
  exact sub_eq_zero.mp (indep_local _ hz ν)

private lemma chosen_local (S : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∃ Λ, HasLambda S Λ) : HasLambda S (LambdaOf S) := by
  classical
  simpa only [LambdaOf, dif_pos h] using h.choose_spec

private lemma value_local {S A : Matrix (Fin 4) (Fin 4) ℝ}
    (h : HasLambda S A) : LambdaOf S = A :=
  unique_local (chosen_local S ⟨A, h⟩) h

private lemma has_neg_local {S A : Matrix (Fin 4) (Fin 4) ℝ}
    (hs : IsUnit S.det) (ha : HasLambda S A) : HasLambda (-S) A := by
  have hi : (-S)⁻¹ = -S⁻¹ := by
    apply Matrix.inv_eq_left_inv
    simp only [neg_mul_neg]
    exact Matrix.nonsing_inv_mul S hs
  intro μ
  rw [hi, neg_mul, neg_mul_neg]
  exact ha μ

theorem solution {S : Matrix (Fin 4) (Fin 4) ℝ} (h : IsPin S) :
    LambdaOf (-S) = LambdaOf S := by
  exact value_local (has_neg_local h.1 (chosen_local S h.2.2))

#print axioms solution

