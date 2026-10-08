-- Prove2me | solution 1 for BoydADMM.Nonconvex.factor_model_partial_minimization
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:37:58.773842+00:00
-- url     : https://prove2.me/submissions/5fec913f-30bb-46b7-bff9-1709669c926d

import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_FactorModel



namespace BoydADMM.Nonconvex

lemma fm_withDiag_split {n : ℕ} (Sigma X : SqMat n) (d : Fin n → ℝ) :
    factorLossWithDiag Sigma X d =
      (1 / 2 : ℝ) * (∑ i, ∑ j, if i ≠ j then (X i j - Sigma i j) ^ 2 else 0) +
      (1 / 2 : ℝ) * ∑ i, (X i i + d i - Sigma i i) ^ 2 := by
  unfold factorLossWithDiag frobSq diag
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : ∀ j, ((X + Matrix.diagonal d - Sigma) i j) ^ 2 =
      (if i ≠ j then (X i j - Sigma i j) ^ 2 else 0) +
      (if i = j then (X i i + d i - Sigma i i) ^ 2 else 0) := by
    intro j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma fm_diag_term (a d : ℝ) (hd : 0 ≤ d) : (max a 0) ^ 2 ≤ (a + d) ^ 2 := by
  rcases le_or_gt a 0 with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg (a + d)]
  · rw [max_eq_left h.le]; nlinarith

lemma fm_withDiag_ge {n : ℕ} (Sigma X : SqMat n) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    factorLossExplicit Sigma X ≤ factorLossWithDiag Sigma X d := by
  rw [fm_withDiag_split]; unfold factorLossExplicit
  have : ∑ i, (max (X i i - Sigma i i) 0) ^ 2 ≤ ∑ i, (X i i + d i - Sigma i i) ^ 2 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := fm_diag_term (X i i - Sigma i i) (d i) (hd i)
    linarith [show X i i - Sigma i i + d i = X i i + d i - Sigma i i by ring]
  linarith

lemma fm_withDiag_opt {n : ℕ} (Sigma X : SqMat n) :
    factorLossWithDiag Sigma X (optimalDiag Sigma X) = factorLossExplicit Sigma X := by
  rw [fm_withDiag_split]; unfold factorLossExplicit optimalDiag
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases le_or_gt (X i i - Sigma i i) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h.le, max_eq_right (by linarith)]; ring

lemma fm_loss_eq {n : ℕ} (Sigma X : SqMat n) :
    factorLoss Sigma X = factorLossExplicit Sigma X := by
  unfold factorLoss
  apply IsLeast.csInf_eq
  refine ⟨⟨optimalDiag Sigma X, fun i => le_max_right _ _, (fm_withDiag_opt Sigma X).symm⟩, ?_⟩
  rintro r ⟨d, hd, rfl⟩
  exact fm_withDiag_ge Sigma X d hd

theorem partial_min_core {n : ℕ} (Sigma X : SqMat n) :
    factorLoss Sigma X = factorLossExplicit Sigma X ∧
    (∀ i, 0 ≤ optimalDiag Sigma X i) ∧
    factorLossWithDiag Sigma X (optimalDiag Sigma X) = factorLoss Sigma X :=
  ⟨fm_loss_eq Sigma X, fun i => le_max_right _ _, by rw [fm_withDiag_opt, fm_loss_eq]⟩

/-- the per-entry objective -/
noncomputable def entryObj {n : ℕ} (Sigma Z U : SqMat n) (rho : ℝ) (X : SqMat n) (i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * (if i ≠ j then (X i j - Sigma i j) ^ 2 else (max (X i j - Sigma i j) 0) ^ 2)
    + (rho / 2) * (X i j - Z i j + U i j) ^ 2

lemma fm_xsub_eq {n : ℕ} (Sigma Z U : SqMat n) (rho : ℝ) (X : SqMat n) :
    xSubproblem Sigma Z U rho X = ∑ i, ∑ j, entryObj Sigma Z U rho X i j := by
  unfold xSubproblem entryObj
  rw [fm_loss_eq]; unfold factorLossExplicit frobSq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∀ i, ∑ j, (if i ≠ j then (X i j - Sigma i j) ^ 2 else (max (X i j - Sigma i j) 0) ^ 2)
      = (∑ j, if i ≠ j then (X i j - Sigma i j) ^ 2 else 0) + (max (X i i - Sigma i i) 0) ^ 2 := by
    intro i
    have : ∀ j, (if i ≠ j then (X i j - Sigma i j) ^ 2 else (max (X i j - Sigma i j) 0) ^ 2)
        = (if i ≠ j then (X i j - Sigma i j) ^ 2 else 0) +
          (if i = j then (max (X i i - Sigma i i) 0) ^ 2 else 0) := by
      intro j; by_cases h : i = j
      · subst h; simp
      · simp [h]
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [h1, Finset.sum_add_distrib]
  simp [Matrix.sub_apply, Matrix.add_apply]
  ring

lemma fm_entry_bound {n : ℕ} (Sigma Z U : SqMat n) (rho : ℝ) (hrho : 0 < rho) (X : SqMat n)
    (i j : Fin n) :
    entryObj Sigma Z U rho (xUpdate Sigma Z U rho) i j + (rho / 2) * (X i j - xUpdate Sigma Z U rho i j) ^ 2
      ≤ entryObj Sigma Z U rho X i j := by
  unfold entryObj xUpdate
  by_cases hij : i = j
  · subst hij
    simp only [ne_eq, not_true_eq_false, if_false, if_true]
    set s := Sigma i i; set v := Z i i - U i i
    have hv : ∀ y : ℝ, y - Z i i + U i i = y - v := fun y => by simp only [v]; ring
    rw [hv, hv]
    set x := X i i
    split_ifs with hs
    · -- x0 = (s + rho v)/(1+rho) ≥ s
      have h1 : (0:ℝ) < 1 + rho := by linarith
      set x0 := (s + rho * v) / (1 + rho) with hx0
      have hx0s : s ≤ x0 := by rw [hx0, le_div_iff₀ h1]; nlinarith
      rw [max_eq_left (by linarith : (0:ℝ) ≤ x0 - s)]
      have key : (s + rho * v) = (1 + rho) * x0 := by rw [hx0]; field_simp
      rcases le_or_gt x s with h | h
      · rw [max_eq_right (by linarith : x - s ≤ 0)]
        -- f(x) = rho/2 (x-v)^2 ; need bound
        nlinarith [sq_nonneg (x - x0), sq_nonneg (x0 - s), mul_pos hrho h1]
      · rw [max_eq_left (show (0:ℝ) ≤ x - s by linarith)]
        nlinarith [sq_nonneg (x - x0), mul_pos hrho h1]
    · push Not at hs
      simp only [sub_self]
      rw [show (max (v - s) 0) = 0 from max_eq_right (by linarith)]
      have : 0 ≤ (max (x - s) 0) ^ 2 := sq_nonneg _
      nlinarith
  · simp only [ne_eq, hij, not_false_eq_true, if_true, if_false]
    have h1 : (0:ℝ) < 1 + rho := by linarith
    set x0 := (Sigma i j + rho * (Z i j - U i j)) / (1 + rho) with hx0
    have key : Sigma i j + rho * (Z i j - U i j) = (1 + rho) * x0 := by rw [hx0]; field_simp
    have e : (1 / 2 : ℝ) * (X i j - Sigma i j) ^ 2 + rho / 2 * (X i j - Z i j + U i j) ^ 2 =
        1 / 2 * (x0 - Sigma i j) ^ 2 + rho / 2 * (x0 - Z i j + U i j) ^ 2 +
          (1 + rho) / 2 * (X i j - x0) ^ 2 := by
      linear_combination (-(X i j - x0)) * key
    rw [e]; nlinarith [sq_nonneg (X i j - x0)]

end BoydADMM.Nonconvex

open BoydADMM.Nonconvex


theorem solution {n : ℕ} (Sigma X : SqMat n)
    (hn : 0 < n) (hSigma : IsSymmetric Sigma) (hX : IsSymmetric X) :
    factorLoss Sigma X = factorLossExplicit Sigma X ∧
    (∀ i, 0 ≤ optimalDiag Sigma X i) ∧
    factorLossWithDiag Sigma X (optimalDiag Sigma X) = factorLoss Sigma X := by
  exact partial_min_core Sigma X
