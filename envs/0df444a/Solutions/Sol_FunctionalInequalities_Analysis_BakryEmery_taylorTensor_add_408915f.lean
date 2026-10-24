-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.taylorTensor_add_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:50:03.262979+00:00
-- url     : https://prove2.me/submissions/3bfba76b-73e4-4a32-b966-bb7571c25356

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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiff_tiltAverage_of_memLp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_exp_mul_norm_of_memLp_408915f

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
/-- `T_d` is additive on `L²(μ)`. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f g : E → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (d : ℕ) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => f x + g x) d = FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ f d + FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ g d := by
  have hint : ∀ φ : E → ℝ, MemLp φ 2 μ → ∀ z : E, Integrable φ (FunctionalInequalities.Analysis.BakryEmery.expTilt μ z) := by
    intro φ hφ z
    have hc : Continuous fun x : E => Real.exp ⟪z, x⟫ := by fun_prop
    have hez : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
      refine (hexp ‖z‖).mono' hc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (real_inner_le_norm z x)
    unfold FunctionalInequalities.Analysis.BakryEmery.expTilt
    rw [integrable_tilted_iff hez]
    refine (FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_408915f μ hexp hφ ‖z‖).mono'
      (hc.aestronglyMeasurable.mul hφ.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    gcongr
    exact real_inner_le_norm z x
  have hsum : FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ (fun x => f x + g x) = FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f + FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ g := by
    funext z
    simp only [FunctionalInequalities.Analysis.BakryEmery.tiltAverage, Pi.add_apply]
    exact integral_add (hint f hf z) (hint g hg z)
  unfold FunctionalInequalities.Analysis.BakryEmery.taylorTensor
  rw [hsum, iteratedFDeriv_add_apply
    ((FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_of_memLp_408915f μ hexp hf).contDiffAt.of_le (by exact_mod_cast le_top))
    ((FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_of_memLp_408915f μ hexp hg).contDiffAt.of_le (by exact_mod_cast le_top)),
    smul_add]
