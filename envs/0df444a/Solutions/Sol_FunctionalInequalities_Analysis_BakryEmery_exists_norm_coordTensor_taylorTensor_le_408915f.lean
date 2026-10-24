-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:45:20.393647+00:00
-- url     : https://prove2.me/submissions/4c413032-ad8d-4ec4-9307-1db7f170582f

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_exists_norm_taylorTensor_le_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_coordTensor_le_408915f

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section IntegralCalculus
omit [CompleteSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Continuity of `T_d` on `L²(μ)` in the Hilbert–Schmidt norm** of the coefficient array (the
norm of BKL (29)), for a probability measure with all exponential moments. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (d : ℕ) :
    ∃ C : ℝ, ∀ f : E → ℝ, MemLp f 2 μ →
      ‖FunctionalInequalities.Analysis.Tensor.coordTensor b (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d)‖ ≤ C * (eLpNorm f 2 μ).toReal := by
    obtain ⟨C, hC⟩ := FunctionalInequalities.Analysis.BakryEmery.exists_norm_taylorTensor_le_408915f μ hexp d
    refine ⟨(Real.sqrt n) ^ d * C, ?_⟩
    intro f hf
    calc
      ‖FunctionalInequalities.Analysis.Tensor.coordTensor b (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d)‖
          ≤ (Real.sqrt n) ^ d * ‖FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d‖ :=
        FunctionalInequalities.Analysis.Tensor.norm_coordTensor_le_408915f b (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d)
      _ ≤ (Real.sqrt n) ^ d * (C * (eLpNorm f 2 μ).toReal) :=
        mul_le_mul_of_nonneg_left (hC f hf) (by positivity)
      _ = ((Real.sqrt n) ^ d * C) * (eLpNorm f 2 μ).toReal := by
        rw [mul_assoc]
