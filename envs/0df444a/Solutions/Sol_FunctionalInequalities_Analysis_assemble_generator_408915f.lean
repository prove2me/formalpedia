-- Prove2me | solution 1 for FunctionalInequalities.Analysis.assemble_generator_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:19:00.773068+00:00
-- url     : https://prove2.me/submissions/4d89c0cd-a36e-4ee4-b869-e83d886e83be

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_ae_fderiv_mongeAmpere_exponent_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_inv_hessianMatrix_mul_of_bounded_compact_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_sum_integral_inv_hessianMatrix_mul_fderiv_eq_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_sum_inv_gradient_test_sub_chain_eq_408915f

section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section WeakThirdDerivativeSymmetry
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section InnerProduct
variable [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.differentiableAt_fderiv_of_differentiableAt_gradient [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx
private lemma FunctionalInequalities.Analysis.hessian_symm_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hu : ContDiff ℝ 1 u)
    (hx : DifferentiableAt ℝ (gradient u) x) :
    hessianMatrix u x i j = hessianMatrix u x j i := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hs :=
    second_derivative_symmetric
      (fun y => (hu.differentiable (by simp) y).hasFDerivAt)
      hfd.hasFDerivAt
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using hs
end InnerProduct
end StructuredSpace
end
end
end WeakThirdDerivativeSymmetry
section GradientDerivativeIdentification
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Stein
/-- The coordinate Hessian of a `C¹` potential is symmetric at every differentiability
point of its gradient, including the zero-dimensional case. -/
theorem FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    (hessianMatrix u x).IsHermitian := by
  change (hessianMatrix u x).conjTranspose = hessianMatrix u x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact hessian_symm_of_gradient_diff hu hx
end
end
end
end GradientDerivativeIdentification
end

noncomputable section
section GeneratorIdentities
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private lemma FunctionalInequalities.Analysis.coord_eq_gradient {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    FunctionalInequalities.Analysis.coord f i x = gradient f x i := by
  calc
    FunctionalInequalities.Analysis.coord f i x =
        ⟪gradient f x, EuclideanSpace.basisFun (Fin n) ℝ i⟫ :=
      inner_gradient_left.symm
    _ = gradient f x i :=
      EuclideanSpace.inner_basisFun_real (Fin n) (gradient f x) i
private lemma FunctionalInequalities.Analysis.drift_eq_sum {n : ℕ}
    (u V f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ V (gradient u x) (gradient f x) =
      ∑ i, FunctionalInequalities.Analysis.coord V i (gradient u x) * FunctionalInequalities.Analysis.coord f i x := by
  calc
    fderiv ℝ V (gradient u x) (gradient f x) =
        ⟪gradient V (gradient u x), gradient f x⟫ :=
      inner_gradient_left.symm
    _ = ∑ i, ⟪gradient V (gradient u x) i, gradient f x i⟫ :=
      PiLp.inner_apply _ _
    _ = ∑ i, FunctionalInequalities.Analysis.coord V i (gradient u x) * FunctionalInequalities.Analysis.coord f i x := by
      simp only [Real.inner_apply, coord_eq_gradient]
private lemma FunctionalInequalities.Analysis.measurable_coord {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) :
    Measurable (FunctionalInequalities.Analysis.coord f i) :=
  (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.basisFun (Fin n) ℝ i)).measurable.comp
      (measurable_fderiv ℝ f)
private lemma FunctionalInequalities.Analysis.coord_bound {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖FunctionalInequalities.Analysis.coord f i x‖ ≤ (L : ℝ) * ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
  ((fderiv ℝ f x).le_opNorm
    (EuclideanSpace.basisFun (Fin n) ℝ i)).trans
      (mul_le_mul_of_nonneg_right
        (norm_fderiv_le_of_lipschitz ℝ hf)
        (norm_nonneg (EuclideanSpace.basisFun (Fin n) ℝ i)))
private lemma FunctionalInequalities.Analysis.integrable_inv_test_derivative {n : ℕ}
    {u F ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G L : NNReal} (hG : LipschitzWith G (gradient u))
    (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (hψ : LipschitzWith L ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin n) :
    Integrable (fun x => (hessianMatrix u x)⁻¹ i j * FunctionalInequalities.Analysis.coord ψ j x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact integrable_inv_hessianMatrix_mul_of_bounded_compact_408915f hG hF hdet
    (measurable_coord ψ j)
    (hψc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ j))
    (coord_bound hψ j) i j
private lemma FunctionalInequalities.Analysis.integrable_inv_chain_test {n : ℕ}
    {u F ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G LF L : NNReal} (hG : LipschitzWith G (gradient u))
    (hF : LipschitzWith LF F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (hψ : LipschitzWith L ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin n) :
    Integrable
      (fun x => (hessianMatrix u x)⁻¹ i j * FunctionalInequalities.Analysis.coord F j x * ψ x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hb (x : EuclideanSpace ℝ (Fin n)) :
      ‖FunctionalInequalities.Analysis.coord F j x * ψ x‖ ≤
        ((LF : ℝ) * ‖EuclideanSpace.basisFun (Fin n) ℝ j‖) * C := by
    rw [norm_mul]
    exact mul_le_mul (coord_bound hF j x) (hC x) (norm_nonneg _)
      (mul_nonneg LF.coe_nonneg (norm_nonneg _))
  have hi :=
    integrable_inv_hessianMatrix_mul_of_bounded_compact_408915f hG hF.continuous hdet
      ((measurable_coord F j).mul hψ.continuous.measurable)
      (hψc.mul_left :
        HasCompactSupport (fun x => FunctionalInequalities.Analysis.coord F j x * ψ x))
      hb i j
  change Integrable
    (fun x => (hessianMatrix u x)⁻¹ i j * (FunctionalInequalities.Analysis.coord F j x * ψ x))
    (volume : Measure (EuclideanSpace ℝ (Fin n))) at hi
  simpa only [mul_assoc] using hi
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
 lemma solution {n : ℕ}
    {u V a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (ht : ∀ i, ∃ L : NNReal,
      LipschitzWith L (FunctionalInequalities.Analysis.weightedTest u a f i) ∧
        HasCompactSupport (FunctionalInequalities.Analysis.weightedTest u a f i))
    (hd : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j,
      FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.weightedTest u a f i) j x =
        Real.exp (-u x) *
          (FunctionalInequalities.Analysis.coord a j x * FunctionalInequalities.Analysis.coord f i x -
            a x * FunctionalInequalities.Analysis.coord u j x * FunctionalInequalities.Analysis.coord f i x +
            a x * FunctionalInequalities.Probability.Stein.hessianMatrix f x j i))
    (hE : Integrable (FunctionalInequalities.Analysis.energyDensity u a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, FunctionalInequalities.Analysis.generatorDensity u V a f x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -∫ x, FunctionalInequalities.Analysis.energyDensity u a f x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let F : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => -u x + V (gradient u x)
  let P (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.weightedTest u a f i) j x
  let Q (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j * FunctionalInequalities.Analysis.coord F j x * FunctionalInequalities.Analysis.weightedTest u a f i x
  let S (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    ∑ i, ∑ j, (P i j x - Q i j x)
  have hP (i j : Fin n) :
      Integrable (P i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨L, hL, hc⟩ := ht i
    exact integrable_inv_test_derivative hG hF.continuous hdet hL hc i j
  have hQ (i j : Fin n) :
      Integrable (Q i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨L, hL, hc⟩ := ht i
    exact integrable_inv_chain_test hG hF hdet hL hc i j
  have hrowInt (i : Fin n) :
      Integrable (fun x => ∑ j, (P i j x - Q i j x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ (fun j _ => (hP i j).sub (hQ i j))
  have hS : Integrable S (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ (fun i _ => hrowInt i)
  have hrow (i : Fin n) :
      (∫ x, ∑ j, (P i j x - Q i j x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 0 := by
    rw [integral_finsetSum Finset.univ
      (f := fun j x => P i j x - Q i j x)
      (fun j _ => (hP i j).sub (hQ i j))]
    have hs (j : Fin n) :
        (∫ x, P i j x - Q i j x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
            (∫ x, P i j x) - ∫ x, Q i j x :=
      integral_sub (hP i j) (hQ i j)
    simp only [hs, Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    obtain ⟨L, hL, hc⟩ := ht i
    exact FunctionalInequalities.Analysis.sum_integral_inv_hessianMatrix_mul_fderiv_eq_408915f hu hG hF hdet hL hc i
  have hz : (∫ x, S x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 0 := by
    change (∫ x, ∑ i, ∑ j, (P i j x - Q i j x)) = 0
    rw [integral_finsetSum Finset.univ
      (f := fun i x => ∑ j, (P i j x - Q i j x))
      (fun i _ => hrowInt i)]
    simp only [hrow, Finset.sum_const_zero]
  have hdall :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j,
        FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.weightedTest u a f i) j x =
          Real.exp (-u x) *
            (FunctionalInequalities.Analysis.coord a j x * FunctionalInequalities.Analysis.coord f i x -
              a x * FunctionalInequalities.Analysis.coord u j x * FunctionalInequalities.Analysis.coord f i x +
              a x * FunctionalInequalities.Probability.Stein.hessianMatrix f x j i) :=
    ae_all_iff.mpr hd
  have heq :
      S =ᵐ[volume] (fun x => FunctionalInequalities.Analysis.energyDensity u a f x + FunctionalInequalities.Analysis.generatorDensity u V a f x) := by
    filter_upwards [hdall, FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_408915f hu hG hV,
      hG.ae_differentiableAt
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))),
      hdet] with x hxD hxF hxG hxdet
    have hA := FunctionalInequalities.Probability.Stein.hessianMatrix_isHermitian_of_differentiableAt_gradient hu hxG
    have hunit : IsUnit (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det := by
      rw [hxdet]
      exact isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)
    have hc := FunctionalInequalities.Analysis.sum_inv_gradient_test_sub_chain_eq_408915f
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x) (FunctionalInequalities.Probability.Stein.hessianMatrix f x) hA hunit
      (a x) (fun i => FunctionalInequalities.Analysis.coord a i x) (fun i => FunctionalInequalities.Analysis.coord u i x)
      (fun i => FunctionalInequalities.Analysis.coord V i (gradient u x)) (fun i => FunctionalInequalities.Analysis.coord f i x)
    calc
      S x =
          Real.exp (-u x) *
            ((∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
                (FunctionalInequalities.Analysis.coord a j x * FunctionalInequalities.Analysis.coord f i x -
                  a x * FunctionalInequalities.Analysis.coord u j x * FunctionalInequalities.Analysis.coord f i x +
                  a x * FunctionalInequalities.Probability.Stein.hessianMatrix f x j i)) -
              (∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
                (-FunctionalInequalities.Analysis.coord u j x +
                  ∑ k, FunctionalInequalities.Probability.Stein.hessianMatrix u x j k * FunctionalInequalities.Analysis.coord V k (gradient u x)) *
                (a x * FunctionalInequalities.Analysis.coord f i x))) := by
        dsimp only [S]
        rw [mul_sub]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [P, Q]
        rw [hxD i j]
        have hj :
            FunctionalInequalities.Analysis.coord F j x =
              -FunctionalInequalities.Analysis.coord u j x +
                ∑ k, FunctionalInequalities.Probability.Stein.hessianMatrix u x j k * FunctionalInequalities.Analysis.coord V k (gradient u x) :=
          hxF j
        rw [hj]
        dsimp only [FunctionalInequalities.Analysis.weightedTest]
        ring
      _ = FunctionalInequalities.Analysis.energyDensity u a f x + FunctionalInequalities.Analysis.generatorDensity u V a f x := by
        rw [hc]
        dsimp only [FunctionalInequalities.Analysis.energyDensity, FunctionalInequalities.Analysis.generatorDensity]
        rw [drift_eq_sum u V f x]
        ring
  have hcombined :
      Integrable (fun x => FunctionalInequalities.Analysis.energyDensity u a f x + FunctionalInequalities.Analysis.generatorDensity u V a f x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hS.congr heq
  have hgen : Integrable (FunctionalInequalities.Analysis.generatorDensity u V a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hi := hcombined.sub hE
    change Integrable
      (fun x => (FunctionalInequalities.Analysis.energyDensity u a f x + FunctionalInequalities.Analysis.generatorDensity u V a f x) -
        FunctionalInequalities.Analysis.energyDensity u a f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) at hi
    simpa only [add_sub_cancel_left] using hi
  have hsum :
      (∫ x, FunctionalInequalities.Analysis.energyDensity u a f x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, FunctionalInequalities.Analysis.generatorDensity u V a f x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 0 := by
    rw [← integral_add hE hgen, ← integral_congr_ae heq]
    exact hz
  linarith
