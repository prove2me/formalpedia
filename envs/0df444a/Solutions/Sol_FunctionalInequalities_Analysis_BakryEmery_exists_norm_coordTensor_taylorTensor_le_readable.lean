-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:21.685231+00:00
-- url     : https://prove2.me/submissions/9efa584c-6fbd-44f2-b9ab-217d1bdcf391

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_exists_norm_taylorTensor_le_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_coordTensor_le_readable

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section IntegralCalculus
omit [CompleteSpace E]
/-- **Continuity of `T_d` on `L²(μ)` in the Hilbert–Schmidt norm** of the coefficient array (the
norm of BKL (29)), for a probability measure with all exponential moments. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (d : ℕ) :
    ∃ C : ℝ, ∀ f : E → ℝ, MemLp f 2 μ →
      ‖FunctionalInequalities.Analysis.Tensor.coordTensor b (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d)‖ ≤ C * (eLpNorm f 2 μ).toReal := by
    obtain ⟨C, hC⟩ := FunctionalInequalities.Analysis.BakryEmery.exists_norm_taylorTensor_le_readable μ hexp d
    refine ⟨(Real.sqrt n) ^ d * C, ?_⟩
    intro f hf
    calc
      ‖FunctionalInequalities.Analysis.Tensor.coordTensor b (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d)‖
          ≤ (Real.sqrt n) ^ d * ‖FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d‖ :=
        FunctionalInequalities.Analysis.Tensor.norm_coordTensor_le_readable b (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d)
      _ ≤ (Real.sqrt n) ^ d * (C * (eLpNorm f 2 μ).toReal) :=
        mul_le_mul_of_nonneg_left (hC f hf) (by positivity)
      _ = ((Real.sqrt n) ^ d * C) * (eLpNorm f 2 μ).toReal := by
        rw [mul_assoc]
