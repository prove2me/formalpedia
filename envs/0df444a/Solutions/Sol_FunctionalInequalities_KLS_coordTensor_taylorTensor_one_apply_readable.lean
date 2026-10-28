-- Prove2me | solution 1 for FunctionalInequalities.KLS.coordTensor_taylorTensor_one_apply_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:54.839439+00:00
-- url     : https://prove2.me/submissions/c9599e59-7f71-4aea-b48a-998429b022b8

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Reduction
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_one_apply_readable

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

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace
/-- Entries of the coordinate array of `T_1 f` for a centered law: `(T_1 f)_j = ∫ ⟪e_j, x⟫ f(x) dμ`. -/
theorem solution {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (hμ2 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
    (hμ0 : ∫ x, x ∂μ = 0) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (i : Fin 1 → Fin n) :
    FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f 1) i =
      ∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ (i 0), x⟫ * f x ∂μ := by
    rw [FunctionalInequalities.Analysis.Tensor.coordTensor_apply]
    have hfun :
        (fun j : Fin 1 => EuclideanSpace.basisFun (Fin n) ℝ (i j)) =
          (fun _ : Fin 1 => EuclideanSpace.basisFun (Fin n) ℝ (i 0)) := by
      funext j
      rw [Subsingleton.elim j 0]
    rw [hfun]
    rw [FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_apply_readable μ hexp hf
      (EuclideanSpace.basisFun (Fin n) ℝ (i 0))]
    have hmean := _root_.integral_inner (𝕜 := ℝ)
      (hμ2.integrable one_le_two)
      (EuclideanSpace.basisFun (Fin n) ℝ (i 0))
    simp only [id_eq] at hmean
    rw [hμ0, inner_zero_right] at hmean
    rw [hmean, mul_zero, sub_zero]
