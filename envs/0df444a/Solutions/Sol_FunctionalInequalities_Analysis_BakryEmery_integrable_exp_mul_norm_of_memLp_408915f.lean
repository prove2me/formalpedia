-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:41:22.811926+00:00
-- url     : https://prove2.me/submissions/f930f260-342f-4f70-bf65-b21e1885366f

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
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Square-integrable functions are integrable against every exponential weight when `μ` is
finite with all exponential moments. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ} (hf : MemLp f 2 μ)
    (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖) * ‖f x‖) μ := by
    have hmeas : AEStronglyMeasurable (fun x : E => Real.exp (r * ‖x‖)) μ :=
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_norm : Continuous (fun x : E => ‖x‖)))).aestronglyMeasurable
    have hsquare :
        Integrable (fun x => (Real.exp (r * ‖x‖)) ^ (2 : ℕ)) μ := by
      convert hexp (2 * r) using 1
      funext x
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hg : MemLp (fun x : E => Real.exp (r * ‖x‖)) 2 μ :=
      (memLp_two_iff_integrable_sq hmeas).2 hsquare
    have hprod :
        Integrable
          ((fun x : E => Real.exp (r * ‖x‖)) * (fun x : E => ‖f x‖)) μ :=
      hg.integrable_mul hf.norm
    have heq :
        (fun x : E => Real.exp (r * ‖x‖)) * (fun x : E => ‖f x‖) =
          (fun x : E => Real.exp (r * ‖x‖) * ‖f x‖) := by
      funext x
      rfl
    exact heq ▸ hprod
