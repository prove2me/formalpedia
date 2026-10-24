-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:44:04.021137+00:00
-- url     : https://prove2.me/submissions/227c7c97-92cb-4c8a-8b5c-fa78d62f85fc

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
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
import Theorems.Thm_FunctionalInequalities_Analysis_inner_iteratedFDeriv_gradient_apply_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_iteratedFDeriv_sub_const_of_pos_408915f

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
section GradientJets
omit [BorelSpace E] in
/-- Literal scalar-cumulant meaning of `cumulantVector`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.cumulantVector_inner (μ : Measure E) (hs : List E) (w : E) :
    ⟪cumulantVector μ hs, w⟫ =
      cumulant μ (hs.length + 1) (Fin.snoc (fun i => hs.get i) w) := by
  rw [cumulantVector, InnerProductSpace.toDual_symm_apply,
    ContinuousMultilinearMap.curryRight_apply]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Jets of the centred CGF gradient are the cumulant Riesz vectors**: for `r ≥ 1`,
`Dʳ(∇Λ − ∇Λ(0))(0)[h] = cumulantVector μ (List.ofFn h)`, i.e. `⟪Dʳv(0)[h], w⟫ = κ_{r+1}(h, w)`. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (r : ℕ) (hr : 1 ≤ r) (h : Fin r → E) :
    iteratedFDeriv ℝ r (fun z : E =>
      gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) z - gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) 0) 0 h =
      FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) (List.ofFn h) := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    let Λ : E → ℝ := FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)
    have hΛ : ContDiff ℝ ∞ Λ := by
      dsimp [Λ]
      exact FunctionalInequalities.Analysis.BakryEmery.contDiff_logLaplace _ (FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp _ hc)
    have hg : ContDiff ℝ ∞ (gradient Λ) := by
      change ContDiff ℝ ∞
        ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ Λ)
      exact
        (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp
          (hΛ.fderiv_right (by simp))
    change
      iteratedFDeriv ℝ r
          (fun z : E => gradient Λ z - gradient Λ 0) 0 h =
        FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) (List.ofFn h)
    rw [FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos_408915f hg (gradient Λ 0) hr 0]
    apply ext_inner_right ℝ
    intro w
    rw [FunctionalInequalities.Analysis.inner_iteratedFDeriv_gradient_apply_408915f hΛ r 0 h w,
      FunctionalInequalities.Analysis.BakryEmery.cumulantVector_inner]
    have haux :
        ∀ (n : ℕ) (hn : n = r) (g : Fin n → E),
          (∀ i, g i = h (Fin.cast hn i)) →
            FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure E) (n + 1) (Fin.snoc g w) =
              iteratedFDeriv ℝ (r + 1) Λ 0 (Fin.snoc h w) := by
      intro n hn g hg'
      subst n
      have hgeq : g = h := by
        funext i
        simpa using hg' i
      unfold FunctionalInequalities.Analysis.BakryEmery.cumulant
      dsimp [Λ]
      rw [hgeq]
    symm
    exact
      haux (List.ofFn h).length List.length_ofFn
        (fun i => (List.ofFn h).get i)
        (fun i => by
          simpa using (List.get_ofFn h i))
