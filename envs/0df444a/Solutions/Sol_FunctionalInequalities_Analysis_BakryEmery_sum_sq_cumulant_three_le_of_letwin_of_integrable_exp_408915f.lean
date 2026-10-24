-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:49:48.429229+00:00
-- url     : https://prove2.me/submissions/95678067-8ef9-4dbb-b22e-886e232d23e7

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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_three_eq_integral_of_integrable_exp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_memLp_of_polynomial_bound_of_integrable_exp_408915f

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
omit [FiniteDimensional ℝ E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.memLp_inner_of_local (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v : E) :
    MemLp (fun x => ⟪v, x⟫) 2 μ := by
  apply memLp_of_polynomial_bound_of_integrable_exp_408915f μ hr hexp (by fun_prop) (C := ‖v‖) (k := 1)
  intro x
  simpa only [pow_one] using
    (norm_inner_le_norm v x).trans
      (mul_le_mul_of_nonneg_left (by linarith : ‖x‖ ≤ 1 + ‖x‖) (norm_nonneg v))
omit [FiniteDimensional ℝ E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.memLp_inner_mul_of_local (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v w : E) :
    MemLp (fun x => ⟪v, x⟫ * ⟪w, x⟫) 2 μ := by
  apply memLp_of_polynomial_bound_of_integrable_exp_408915f μ hr hexp (by fun_prop)
    (C := ‖v‖ * ‖w‖) (k := 2)
  intro x
  calc
    ‖⟪v, x⟫ * ⟪w, x⟫‖ ≤ (‖v‖ * ‖x‖) * (‖w‖ * ‖x‖) := by
      rw [norm_mul]
      exact mul_le_mul (norm_inner_le_norm v x) (norm_inner_le_norm w x)
        (norm_nonneg _) (by positivity)
    _ = (‖v‖ * ‖w‖) * ‖x‖ ^ 2 := by ring
    _ ≤ (‖v‖ * ‖w‖) * (1 + ‖x‖) ^ 2 := by gcongr; linarith
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **BKL Lemma 4.2, local-moment form**: for a centered isotropic law with one exponential moment and
the Letwin quadratic bound, `∑_{jk} κ₃(u, e_j, e_k)² ≤ 8‖u‖²` (the contraction argument of `Cumulant`,
with all `L²` facts from the single radius). -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫) (hL : FunctionalInequalities.Analysis.BakryEmery.LetwinQuadraticBound μ) (u : E) :
    ∑ j, ∑ k, FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3 ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2 ≤
      8 * ‖u‖ ^ 2 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let C := fun j k => ∫ x, ⟪u, x⟫ * ⟪b j, x⟫ * ⟪b k, x⟫ ∂μ
  let S : ℝ := ∑ j, ∑ k, C j k ^ 2
  let M : E →L[ℝ] E := ∑ j, ∑ k, C j k • (innerSL ℝ (b k)).smulRight (b j)
  let Q : E → ℝ := fun x => ⟪M x, x⟫
  let f : E → ℝ := fun x => ⟪u, x⟫
  let q : E → ℝ := fun x => Q x - ∫ y, Q y ∂μ
  have hC : ∀ j k, C j k = C k j := by
    intro j k
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hMxy (x y : E) :
      ⟪M x, y⟫ = ∑ j, ∑ k, C j k * ⟪b k, x⟫ * ⟪b j, y⟫ := by
    simp [M, sum_inner, real_inner_smul_left, mul_assoc]
  have hM : IsSelfAdjoint M := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
    intro x y
    change ⟪M x, y⟫ = ⟪x, M y⟫
    conv_rhs => rw [real_inner_comm]
    rw [hMxy, hMxy, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hC k j]
    ring
  have hMij (i j) : ⟪M (b i), b j⟫ = C j i := by
    rw [hMxy]
    simp [b.inner_eq_ite]
  have hvar : ∫ x, q x ^ 2 ∂μ ≤ 8 * S := by
    simpa only [q, Q, hMij, hC, S, b] using hL M hM
  have hf : MemLp f 2 μ := memLp_inner_of_local μ hr hexp u
  have hQ : MemLp Q 2 μ := by
    have heq : Q = fun x => ∑ j, ∑ k, C j k * (⟪b k, x⟫ * ⟪b j, x⟫) := by
      funext x
      simp only [Q, hMxy, mul_assoc]
    rw [heq]
    exact memLp_finsetSum _ fun j _ =>
      memLp_finsetSum _ fun k _ =>
        (memLp_inner_mul_of_local μ hr hexp (b k) (b j)).const_mul (C j k)
  have hq : MemLp q 2 μ := hQ.sub (memLp_const _)
  have hcross : ∫ x, f x * q x ∂μ = S := by
    have hprod : ∀ j k, Integrable (fun x => ⟪u, x⟫ * (⟪b k, x⟫ * ⟪b j, x⟫)) μ :=
      fun j k => hf.integrable_mul (memLp_inner_mul_of_local μ hr hexp (b k) (b j))
    have hprodC : ∀ j k, Integrable (fun x => C j k * (⟪u, x⟫ * (⟪b k, x⟫ * ⟪b j, x⟫))) μ :=
      fun j k => (hprod j k).const_mul _
    have hsum : Integrable (fun x => f x * Q x) μ := hf.integrable_mul hQ
    simp only [q, mul_sub]
    rw [integral_sub hsum ((hf.integrable (by norm_num)).mul_const (∫ y, Q y ∂μ)),
      integral_mul_const]
    simp only [f, hc, zero_mul, sub_zero]
    simp_rw [Q, hMxy, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        have heq : (fun x => ⟪u, x⟫ * (C j k * ⟪b k, x⟫ * ⟪b j, x⟫)) =
            fun x => C j k * (⟪u, x⟫ * ⟪b j, x⟫ * ⟪b k, x⟫) := by
          funext x; ring
        rw [heq, integral_const_mul]
        exact (pow_two (C j k)).symm
      · intro k _
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hprodC j k
    · intro j _
      apply integrable_finsetSum
      intro k _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hprodC j k
  have hf2 : Integrable (fun x => f x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hq2 : Integrable (fun x => q x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hq.aestronglyMeasurable).1 hq
  have hsq : 0 ≤ (∫ x, q x ^ 2 ∂μ) - 16 * S + 64 * ‖u‖ ^ 2 := by
    have hn := integral_nonneg (μ := μ) (f := fun x => (q x - 8 * f x) ^ 2)
      (fun x => sq_nonneg _)
    have heq : (fun x => (q x - 8 * f x) ^ 2) =
        fun x => q x ^ 2 - 16 * (f x * q x) + 64 * f x ^ 2 := by
      funext x; ring
    rw [heq, integral_add (f := fun x => q x ^ 2 - 16 * (f x * q x))
      (g := fun x => 64 * f x ^ 2)
      (hq2.sub ((hf.integrable_mul hq).const_mul 16))
      (hf2.const_mul 64),
      integral_sub (f := fun x => q x ^ 2) (g := fun x => 16 * (f x * q x))
      hq2 ((hf.integrable_mul hq).const_mul 16),
      integral_const_mul, integral_const_mul, hcross] at hn
    have he : ∫ x, f x ^ 2 ∂μ = ‖u‖ ^ 2 := by
      simpa only [f, pow_two, real_inner_self_eq_norm_sq] using hiso u u
    rwa [he] at hn
  have hκ (v w : E) :
      FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3 ![u, v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ :=
    FunctionalInequalities.Analysis.BakryEmery.cumulant_three_eq_integral_of_integrable_exp_408915f μ hr hexp hc u v w
  simp_rw [hκ]
  change S ≤ 8 * ‖u‖ ^ 2
  linarith
