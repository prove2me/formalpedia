-- Prove2me | solution 1 for DynAssortPers.Regret.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:00:23.474335+00:00
-- url     : https://prove2.me/submissions/2c0dc69e-c798-4b9f-926a-b889acf06b8d

import Mathlib
import Definitions.Def_DynAssortPers_Regret_Estimator
import Theorems.Thm_matrix_trace_duality_inequality
import Theorems.Thm_nuclear_norm_dual_achiever_contraction

open DynAssortPers.Regret MatrixCompletion

namespace DAPl5

lemma spectralNorm_neg {m n : ℕ} (A : RealMatrix m n) :
    MatrixCompletion.spectralNorm (-A) = MatrixCompletion.spectralNorm A := by
  unfold MatrixCompletion.spectralNorm
  rw [map_neg, map_neg, norm_neg]

lemma matrixInner_neg {m n : ℕ} (A B : RealMatrix m n) :
    matrixInner (-A) B = -matrixInner A B := by
  unfold matrixInner
  simp [Finset.sum_neg_distrib]

lemma matrixInner_sub {m n : ℕ} (A B C : RealMatrix m n) :
    matrixInner A (B - C) = matrixInner A B - matrixInner A C := by
  unfold matrixInner
  simp [mul_sub, Finset.sum_sub_distrib]

lemma nuclearNorm_nonneg {m n : ℕ} (A : RealMatrix m n) : 0 ≤ nuclearNorm A := by
  unfold nuclearNorm Finsupp.sum
  exact Finset.sum_nonneg (fun i _ => LinearMap.singularValues_nonneg _ i)

/-- `‖X‖_* − ‖Y‖_* ≤ ‖Y − X‖_*`, from the dual achiever and trace duality. -/
lemma nuclearNorm_sub_le {m n : ℕ} (X Y : RealMatrix m n) :
    nuclearNorm X - nuclearNorm Y ≤ nuclearNorm (Y - X) := by
  obtain ⟨Z, hZ, hZX⟩ := nuclear_norm_dual_achiever_contraction X
  have h1 := matrix_trace_duality_inequality Z Y
  have h2 := matrix_trace_duality_inequality (-Z) (Y - X)
  rw [spectralNorm_neg, matrixInner_neg, matrixInner_sub] at h2
  have hY := nuclearNorm_nonneg Y
  have hD := nuclearNorm_nonneg (Y - X)
  have hZ0 : 0 ≤ MatrixCompletion.spectralNorm Z := by unfold MatrixCompletion.spectralNorm; exact norm_nonneg _
  have e1 : MatrixCompletion.spectralNorm Z * nuclearNorm Y ≤ nuclearNorm Y := by nlinarith
  have e2 : MatrixCompletion.spectralNorm Z * nuclearNorm (Y - X) ≤ nuclearNorm (Y - X) := by nlinarith
  linarith

theorem l5 {m n : ℕ} (O : List (Obs m n)) (lam α : ℝ) (hlam : 0 < lam)
    (Θs Θh : RealMatrix m n)
    (hΘs : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (hΘh : IsEstimate O lam α Θh) :
    bregman O Θs (Θh - Θs) ≤
        spectralNorm (lossGrad O Θs) * nuclearNorm (Θh - Θs) +
          lam * (nuclearNorm Θs - nuclearNorm Θh) ∧
      spectralNorm (lossGrad O Θs) * nuclearNorm (Θh - Θs) +
          lam * (nuclearNorm Θs - nuclearNorm Θh) ≤
        (spectralNorm (lossGrad O Θs) + lam) * nuclearNorm (Θh - Θs) := by
  refine ⟨?_, ?_⟩
  · have hopt := hΘh.2 Θs hΘs
    have hdual := matrix_trace_duality_inequality (-lossGrad O Θs) (Θh - Θs)
    rw [spectralNorm_neg, matrixInner_neg] at hdual
    unfold bregman
    rw [add_sub_cancel]
    linarith
  · have := nuclearNorm_sub_le Θs Θh
    nlinarith

end DAPl5

theorem solution {m n : ℕ} (O : List (Obs m n)) (lam α : ℝ) (hlam : 0 < lam)
    (Θs Θh : RealMatrix m n)
    (hΘs : entrySupNorm Θs ≤ α / Real.sqrt ((m : ℝ) * n))
    (hΘh : IsEstimate O lam α Θh) :
    bregman O Θs (Θh - Θs) ≤
        spectralNorm (lossGrad O Θs) * nuclearNorm (Θh - Θs) +
          lam * (nuclearNorm Θs - nuclearNorm Θh) ∧
      spectralNorm (lossGrad O Θs) * nuclearNorm (Θh - Θs) +
          lam * (nuclearNorm Θs - nuclearNorm Θh) ≤
        (spectralNorm (lossGrad O Θs) + lam) * nuclearNorm (Θh - Θs) :=
  DAPl5.l5 O lam α hlam Θs Θh hΘs hΘh
