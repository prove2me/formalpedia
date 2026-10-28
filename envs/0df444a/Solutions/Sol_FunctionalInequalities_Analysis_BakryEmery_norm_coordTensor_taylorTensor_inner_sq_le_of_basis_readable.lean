-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le_of_basis_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:21.688693+00:00
-- url     : https://prove2.me/submissions/d3a04e4e-0a7a-44b4-9fc6-23eacd3705af

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_inner_eq_cumulant_readable

section
noncomputable section
open Finset
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem FunctionalInequalities.Analysis.Tensor.coordTensor_apply {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (i : Fin k → Fin n) :
    coordTensor b Φ i = Φ (fun j => b (i j)) := by
  rfl
end
end
end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section CumulantEstimates
omit [CompleteSpace E]
/-- **Linear-function step in an arbitrary orthonormal basis** (BKL p. 30): the special case
`norm_coordTensor_taylorTensor_inner_sq_le` with `stdOrthonormalBasis ℝ E` replaced by any orthonormal
basis `bE`. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {m : ℕ}
    (bE : OrthonormalBasis (Fin m) ℝ E) {d : ℕ} {b : ℝ}
    (hR : ∀ u : E, ∑ J : Fin d → Fin m,
      FunctionalInequalities.Analysis.BakryEmery.cumulant μ (d + 1) (Fin.cons u fun k => bE (J k)) ^ 2 ≤ b * ‖u‖ ^ 2) (v : E) :
    ‖FunctionalInequalities.Analysis.Tensor.coordTensor bE (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => ⟪v, x⟫) d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    have hcoord :
        ∀ J : Fin d → Fin m,
          (FunctionalInequalities.Analysis.Tensor.coordTensor (bE)
              (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => ⟪v, x⟫) d)).ofLp J =
            (d.factorial : ℝ)⁻¹ *
              FunctionalInequalities.Analysis.BakryEmery.cumulant μ (d + 1)
                (Fin.cons v (fun k => bE (J k))) := by
      intro J
      simp [FunctionalInequalities.Analysis.Tensor.coordTensor_apply, FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant_readable, hexp]
    rw [EuclideanSpace.norm_sq_eq]
    calc
      ∑ J : Fin d → Fin m,
          ‖(FunctionalInequalities.Analysis.Tensor.coordTensor (bE)
              (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => ⟪v, x⟫) d)).ofLp J‖ ^ 2 =
        ((d.factorial : ℝ)⁻¹) ^ 2 *
          ∑ J : Fin d → Fin m,
            FunctionalInequalities.Analysis.BakryEmery.cumulant μ (d + 1)
              (Fin.cons v (fun k => bE (J k))) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hcoord J, norm_mul]
        simp [Real.norm_eq_abs, sq_abs, mul_pow]
      _ ≤ ((d.factorial : ℝ)⁻¹) ^ 2 * (b * ‖v‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left (hR v) (sq_nonneg _)
      _ = b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2 := by
        simp [div_eq_mul_inv, inv_pow]
        ring
