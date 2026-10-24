-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.directional_centeredGradient_logLaplace_zero_of_compact_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:45:19.063528+00:00
-- url     : https://prove2.me/submissions/f3725ebc-553e-4a56-a938-875ace6cd477

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact_408915f

section
noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- The directional list convention is exactly the raw iterated Fréchet derivative. -/
theorem FunctionalInequalities.Analysis.directional_ofFn {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) f x = iteratedFDeriv ℝ m f x h := by
  induction m generalizing x with
  | zero => simp [directional]
  | succ m IH =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directional (List.ofFn (Fin.tail h)) f) x (h 0) = _
    have he : directional (List.ofFn (Fin.tail h)) f =
        fun y => iteratedFDeriv ℝ m f y (Fin.tail h) := funext (fun y => IH (Fin.tail h) y)
    rw [he]
    exact ((hf.differentiable_iteratedFDeriv (m := m)
      (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)) x).iteratedFDeriv_succ_apply_left').symm
end
end
end
end

section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section CompactSupport
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
/-- A law with compact support has every exponential moment. -/
theorem FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp (μ : Measure F) [IsFiniteMeasure μ]
    (hc : IsCompact μ.support) (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖)) μ := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : F)
  refine (integrable_const (Real.exp (|r| * max R 0))).mono' (by fun_prop) ?_
  filter_upwards [μ.support_mem_ae] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    r * ‖x‖ ≤ |r| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |r| * max R 0 := by
      gcongr
      exact (by simpa using hR hx : ‖x‖ ≤ R).trans (le_max_left _ _)
end CompactSupport
end
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- Directional derivatives at `0` of the centred CGF gradient: `0` for the empty list, `κ_{|l|+1}(l, ·)` otherwise. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (l : List E) :
    FunctionalInequalities.Analysis.directional l (fun z : E =>
        gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) z - gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) 0) 0 =
      if l = [] then 0 else FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) l := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    have hΛ : ContDiff ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) :=
      FunctionalInequalities.Analysis.BakryEmery.contDiff_logLaplace _ (FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp _ hc)
    have hg : ContDiff ℝ ∞ (gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E))) := by
      change
        ContDiff ℝ ∞
          ((InnerProductSpace.toDual ℝ E).symm ∘
            fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)))
      exact
        (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp
          (hΛ.fderiv_right (by simp))
    have hv : ContDiff ℝ ∞ (fun z : E =>
        gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) z -
          gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) 0) :=
      hg.sub contDiff_const
    split_ifs with hl
    · subst hl
      change _ - _ = 0
      exact sub_self _
    · have h1 := FunctionalInequalities.Analysis.directional_ofFn hv l.length l.get 0
      rw [List.ofFn_get] at h1
      rw [h1,
        FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact_408915f μ hc _
          (List.length_pos_iff.mpr hl) _, List.ofFn_get]
