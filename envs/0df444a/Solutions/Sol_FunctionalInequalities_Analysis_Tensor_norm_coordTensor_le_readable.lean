-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.norm_coordTensor_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:16.108849+00:00
-- url     : https://prove2.me/submissions/fd2ca6ab-2bdf-47a6-b787-c39e5435ba55

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients

noncomputable section
open Finset
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem FunctionalInequalities.Analysis.Tensor.coordTensor_apply {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (i : Fin k → Fin n) :
    coordTensor b Φ i = Φ (fun j => b (i j)) := by
  rfl
/-- `‖coordTensor b Φ‖ ≤ (√n)^k ‖Φ‖`. -/
theorem solution {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ‖FunctionalInequalities.Analysis.Tensor.coordTensor b Φ‖ ≤ Real.sqrt n ^ k * ‖Φ‖ := by
    have hbound : ∀ i : Fin k → Fin n, ‖Φ (fun j => b (i j))‖ ≤ ‖Φ‖ := by
      intro i
      calc
        ‖Φ (fun j => b (i j))‖ ≤ ‖Φ‖ * ∏ j, ‖b (i j)‖ := Φ.le_opNorm _
        _ = ‖Φ‖ := by
          simp [OrthonormalBasis.norm_eq_one]
    have hsqrt : ∀ m : ℕ, Real.sqrt ((n : ℝ) ^ m) = Real.sqrt n ^ m := by
      intro m
      induction m with
      | zero =>
          simp
      | succ m ih =>
          rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
    calc
      ‖FunctionalInequalities.Analysis.Tensor.coordTensor b Φ‖ =
          Real.sqrt (∑ i : Fin k → Fin n, ‖Φ (fun j => b (i j))‖ ^ 2) := by
        rw [EuclideanSpace.norm_eq]
        simp [FunctionalInequalities.Analysis.Tensor.coordTensor_apply]
      _ ≤ Real.sqrt (∑ i : Fin k → Fin n, ‖Φ‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i hi
        have hi' := hbound i
        nlinarith [norm_nonneg (Φ (fun j => b (i j))), norm_nonneg Φ]
      _ = Real.sqrt n ^ k * ‖Φ‖ := by
        rw [show (∑ i : Fin k → Fin n, ‖Φ‖ ^ 2) =
            (n : ℝ) ^ k * ‖Φ‖ ^ 2 by
          simp [Finset.sum_const]]
        rw [Real.sqrt_mul (by positivity), hsqrt]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg Φ)]
