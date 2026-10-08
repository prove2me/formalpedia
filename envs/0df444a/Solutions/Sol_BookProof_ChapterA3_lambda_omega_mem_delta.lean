-- Prove2me | solution 1 for BookProof.ChapterA3.lambda_omega_mem_delta
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:55:43.458544+00:00
-- url     : https://prove2.me/submissions/14ff6cc3-9574-4519-a069-471a36f7fa22

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

private lemma has_one : HasLambda (1 : Matrix (Fin 4) (Fin 4) ℝ) 1 := by
  intro μ
  simp [Matrix.one_apply]

private lemma square_a0 : omegaA0 * omegaA0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma inverse_a0 : omegaA0⁻¹ = -omegaA0 := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul, square_a0, neg_neg]

private lemma has_a0 : HasLambda omegaA0 minkowskiMat := by
  intro μ
  rw [inverse_a0]
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private lemma square_a5 : omegaA5 * omegaA5 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma inverse_a5 : omegaA5⁻¹ = -omegaA5 := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul, square_a5, neg_neg]

private lemma has_a5 : HasLambda omegaA5 (-1) := by
  intro μ
  rw [inverse_a5]
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private lemma square_g05 : omegaG05 * omegaG05 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma inverse_g05 : omegaG05⁻¹ = -omegaG05 := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul, square_g05, neg_neg]

private lemma has_g05 : HasLambda omegaG05 (-minkowskiMat) := by
  intro μ
  rw [inverse_g05]
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private lemma neg_value_local {S A : Matrix (Fin 4) (Fin 4) ℝ}
    (hs : S⁻¹ * S = 1) (ha : HasLambda S A) : LambdaOf (-S) = A := by
  apply value_local
  have hi : (-S)⁻¹ = -S⁻¹ := by
    apply Matrix.inv_eq_left_inv
    simpa only [neg_mul_neg] using hs
  intro μ
  rw [hi, neg_mul, neg_mul_neg]
  exact ha μ

private lemma left_a0 : omegaA0⁻¹ * omegaA0 = 1 := by
  rw [inverse_a0, neg_mul, square_a0, neg_neg]

private lemma left_a5 : omegaA5⁻¹ * omegaA5 = 1 := by
  rw [inverse_a5, neg_mul, square_a5, neg_neg]

private lemma left_g05 : omegaG05⁻¹ * omegaG05 = 1 := by
  rw [inverse_g05, neg_mul, square_g05, neg_neg]

theorem solution : ∀ S ∈ OmegaPin, LambdaOf S ∈ LorentzDelta := by
  intro S hS
  simp only [OmegaPin, Set.mem_insert_iff, Set.mem_singleton_iff] at hS
  rcases hS with h | h | h | h | h | h | h | h <;> subst S
  · rw [value_local has_one]
    simp [LorentzDelta]
  · rw [neg_value_local (by simp) has_one]
    simp [LorentzDelta]
  · rw [value_local has_a0]
    simp [LorentzDelta]
  · rw [neg_value_local left_a0 has_a0]
    simp [LorentzDelta]
  · rw [value_local has_g05]
    simp [LorentzDelta]
  · rw [neg_value_local left_g05 has_g05]
    simp [LorentzDelta]
  · rw [value_local has_a5]
    simp [LorentzDelta]
  · rw [neg_value_local left_a5 has_a5]
    simp [LorentzDelta]

#print axioms solution

