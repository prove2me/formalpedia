-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.inner_cumulantVector_single_ringInverse_cumulantVector_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:45:58.147472+00:00
-- url     : https://prove2.me/submissions/0cad879b-3ce1-4a31-8e82-1484500ce44e

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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_two_eq_centered_moment_of_integrable_exp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_memLp_of_polynomial_bound_of_integrable_exp_408915f

section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The covariance operator is self-adjoint. -/
theorem FunctionalInequalities.Covariance.operator_isSelfAdjoint (μ : Measure E) : IsSelfAdjoint (Covariance.operator μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪Covariance.operator μ x, y⟫ = ⟪x, Covariance.operator μ y⟫
  calc
    ⟪Covariance.operator μ x, y⟫ = covarianceBilin μ x y := Covariance.operator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = ⟪Covariance.operator μ y, x⟫ := (Covariance.operator_inner μ y x).symm
    _ = ⟪x, Covariance.operator μ y⟫ := real_inner_comm _ _
end
end

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
section SecondCumulant
/-- One exponential moment gives `id ∈ L²(μ)`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.memLp_id_two_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    MemLp id 2 μ := by
  have hn : MemLp (fun x : E => ‖x‖) 2 μ := by
    apply memLp_of_polynomial_bound_of_integrable_exp_408915f μ hr hexp continuous_norm (C := 1) (k := 1)
    intro x
    simp only [norm_norm, pow_one, one_mul]
    linarith
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact (memLp_two_iff_integrable_sq hn.aestronglyMeasurable).1 hn
/-- The second cumulant is the covariance pairing `⟪Cov(μ) u, v⟫`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_covariance_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u v : E) :
    cumulant μ 2 ![u, v] = ⟪Covariance.operator μ u, v⟫ := by
  have h2 := memLp_id_two_of_integrable_exp μ hr hexp
  have hX : MemLp (fun x => ⟪u, x⟫) 2 μ := by
    simpa only [id_eq] using h2.const_inner (𝕜 := ℝ) u
  have hY : MemLp (fun x => ⟪v, x⟫) 2 μ := by
    simpa only [id_eq] using h2.const_inner (𝕜 := ℝ) v
  rw [Covariance.operator_inner, ProbabilityTheory.covarianceBilin_apply_eq_cov h2,
    ProbabilityTheory.covariance_eq_sub hX hY]
  exact cumulant_two_eq_centered_moment_of_integrable_exp_408915f μ hr hexp u v
end SecondCumulant
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
end GradientJets
section SingletonAllocation
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Singleton allocation of (74)** (BKL arXiv:2610.05474v1, p. 21): for a compactly supported law whose covariance
`A` is a unit, `⟪κ₂(w,·), A⁻¹ κ_{|hs|+1}(hs,·)⟫ = κ_{|hs|+1}(hs, w)`, the order-`(|hs|+1)` cumulant with `w` in the
last slot. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hA : IsUnit (FunctionalInequalities.Covariance.operator (μ : Measure E)))
    (hs : List E) (w : E) :
    ⟪FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) [w],
        Ring.inverse (FunctionalInequalities.Covariance.operator (μ : Measure E)) (FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) hs)⟫ =
      FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure E) (hs.length + 1) (Fin.snoc (fun i => hs.get i) w) := by
    have hA2 :
        FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) [w] =
          FunctionalInequalities.Covariance.operator (μ : Measure E) w := by
      apply ext_inner_right ℝ
      intro u
      rw [FunctionalInequalities.Analysis.BakryEmery.cumulantVector_inner]
      have hv :
          Fin.snoc (fun i => [w].get i) u = ![w, u] := by
        funext i
        fin_cases i <;> rfl
      rw [hv]
      change FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure E) 2 (![w, u]) =
        ⟪FunctionalInequalities.Covariance.operator (μ : Measure E) w, u⟫
      rw [FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_covariance_of_integrable_exp
        (μ := μ) (hr := one_pos)
        (FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp _ hc 1) w u]

    have hsa : IsSelfAdjoint (FunctionalInequalities.Covariance.operator (μ : Measure E)) :=
      FunctionalInequalities.Covariance.operator_isSelfAdjoint (μ : Measure E)

    have hsymm (x y : E) :
        ⟪FunctionalInequalities.Covariance.operator (μ : Measure E) x, y⟫ =
          ⟪x, FunctionalInequalities.Covariance.operator (μ : Measure E) y⟫ := by
      exact
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) x y

    have hunit (u : E) :
        FunctionalInequalities.Covariance.operator (μ : Measure E)
            (Ring.inverse (FunctionalInequalities.Covariance.operator (μ : Measure E)) u) = u := by
      have h :=
        congrArg (fun T : E →L[ℝ] E => T u)
          (Ring.mul_inverse_cancel (FunctionalInequalities.Covariance.operator (μ : Measure E)) hA)
      simpa using h

    calc
      ⟪FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) [w],
          Ring.inverse (FunctionalInequalities.Covariance.operator (μ : Measure E))
            (FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) hs)⟫ =
          ⟪FunctionalInequalities.Covariance.operator (μ : Measure E) w,
            Ring.inverse (FunctionalInequalities.Covariance.operator (μ : Measure E))
              (FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) hs)⟫ := by
            rw [hA2]
      _ =
          ⟪w, FunctionalInequalities.Covariance.operator (μ : Measure E)
            (Ring.inverse (FunctionalInequalities.Covariance.operator (μ : Measure E))
              (FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) hs))⟫ := by
            exact hsymm w
              (Ring.inverse (FunctionalInequalities.Covariance.operator (μ : Measure E))
                (FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) hs))
      _ = ⟪w, FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) hs⟫ := by
        rw [hunit]
      _ = ⟪FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) hs, w⟫ := by
        rw [real_inner_comm]
      _ = FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure E) (hs.length + 1)
          (Fin.snoc (fun i => hs.get i) w) := by
        rw [FunctionalInequalities.Analysis.BakryEmery.cumulantVector_inner]
