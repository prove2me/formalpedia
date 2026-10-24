-- Prove2me | solution 1 for FunctionalInequalities.Analysis.letwin_trace_weighted_slices_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:41:51.002896+00:00
-- url     : https://prove2.me/submissions/26bb0ff9-a74e-4a93-93f2-7073e27727fc

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing

open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section TensorComparison
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
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
