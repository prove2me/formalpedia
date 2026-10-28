-- Prove2me | solution 1 for FunctionalInequalities.Analysis.letwin_trace_weighted_slices_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:50.850444+00:00
-- url     : https://prove2.me/submissions/bf6ebb12-fede-4b6a-8f4f-099b6cd01449

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Trace_Energy

open Matrix
section TensorComparison
 lemma solution {n : ℕ}
    (P A C : Matrix (Fin n) (Fin n) ℝ)
    (V : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ k, (A * (∑ a, P k a • V a) * C *
      (∑ b, P k b • V b)).trace) =
      ∑ a, ∑ b, (Pᵀ * P) a b * (A * V a * C * V b).trace := by
  classical
  have expand (x : Fin n → ℝ) :
      (A * (∑ a, x a • V a) * C * (∑ b, x b • V b)).trace =
        ∑ a, ∑ b, (x a * x b) * (A * V a * C * V b).trace := by
    have hf :
        A * (∑ a, x a • V a) * C = ∑ a, x a • (A * V a * C) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_smul_comm, smul_mul_assoc]
    have hm :
        A * (∑ a, x a • V a) * C * (∑ b, x b • V b) =
          ∑ a, ∑ b, (x a * x b) • (A * V a * C * V b) := by
      rw [hf, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hm]
    simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  calc
    (∑ k, (A * (∑ a, P k a • V a) * C *
        (∑ b, P k b • V b)).trace) =
        ∑ k, ∑ a, ∑ b, (P k a * P k b) * (A * V a * C * V b).trace := by
      apply Finset.sum_congr rfl
      intro k _
      exact expand (fun a => P k a)
    _ = ∑ a, ∑ b, ∑ k,
        (P k a * P k b) * (A * V a * C * V b).trace := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (Pᵀ * P) a b * (A * V a * C * V b).trace := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_mul]
      rfl
