-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_of_contDiff_one_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:40:43.182996+00:00
-- url     : https://prove2.me/submissions/8ba0bc2f-b216-4ea8-a574-6058f3210170

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
import Theorems.Thm_FunctionalInequalities_Analysis_assemble_generator_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integrable_inv_hessianMatrix_mul_of_bounded_compact_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_exists_lipschitzWith_smul_of_locallyLipschitz_408915f

noncomputable section
section WeightedGradientTest
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
/-- Compactly supported weighted derivative test for the weak Letwin generator identity.
No global bound on the gradient of w is assumed. -/
private theorem FunctionalInequalities.Analysis.exists_lipschitz_compact_exp_gradient_test {n : ℕ}
    {u w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w)) (i : Fin n) :
    ∃ L : NNReal,
      LipschitzWith L (fun x => η x * Real.exp (-u x) *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) ∧
      HasCompactSupport (fun x => η x * Real.exp (-u x) *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  let γ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => η x * Real.exp (-u x)
  have hγ : ContDiff ℝ 1 γ := hη.mul hu.neg.exp
  have hγc : HasCompactSupport γ := hηc.mul_right
  obtain ⟨Kγ, hKγ⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hγc hγ one_ne_zero
  let e : EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.basisFun (Fin n) ℝ i
  have hcoord :
      LipschitzWith (‖(innerSL ℝ) e‖₊ * Gw)
        (fun x => fderiv ℝ w x e) := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) e).lipschitz.comp hGw)
  obtain ⟨⟨L, hL⟩, _⟩ :=
    FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz_408915f
      hKγ hγc hcoord.locallyLipschitz
  refine ⟨L, ?_, ?_⟩
  · simpa only [smul_eq_mul] using hL
  · exact hγc.mul_right
end
end
end WeightedGradientTest
section WeightedGradientTestDerivative
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
private lemma FunctionalInequalities.Analysis.differentiableAt_fderiv_of_differentiableAt_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx
private lemma FunctionalInequalities.Analysis.hessian_coord_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      hessianMatrix u x i j := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ j) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j)).differentiableAt
  have h := fderiv_clm_apply hfd hc
  have h' := congrArg
    (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using h'
/-- Almost-everywhere derivative of the actual weighted gradient test for Letwin (2.2).
Only C1 u and eta and a Lipschitz gradient of w are needed. -/
private theorem FunctionalInequalities.Analysis.ae_fderiv_exp_gradient_test {n : ℕ}
    {u w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η)
    {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w)) (i : Fin n) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
      fderiv ℝ (fun y => η y * Real.exp (-u y) *
        fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        Real.exp (-u x) *
          (fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ j) *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) -
            η x * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) +
            η x * hessianMatrix w x j i) := by
  filter_upwards [hGw.ae_differentiableAt
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
  have hux : DifferentiableAt ℝ u x :=
    (hu.differentiable one_ne_zero).differentiableAt
  have hηx : DifferentiableAt ℝ η x :=
    (hη.differentiable one_ne_zero).differentiableAt
  have hfd : DifferentiableAt ℝ (fderiv ℝ w) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ i) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i)).differentiableAt
  have hcomponent :
      DifferentiableAt ℝ
        (fun y => fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x :=
    hfd.clm_apply hc
  have he :
      fderiv ℝ (fun y => η y * Real.exp (-u y) *
        fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x =
      (η x * Real.exp (-u x)) •
          fderiv ℝ
            (fun y => fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x +
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) •
          (η x • (Real.exp (-u x) • (-fderiv ℝ u x)) +
            Real.exp (-u x) • fderiv ℝ η x) :=
    ((hηx.hasFDerivAt.mul hux.hasFDerivAt.neg.exp).mul
      hcomponent.hasFDerivAt).fderiv
  intro j
  rw [he]
  simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul]
  rw [hessian_coord_of_gradient_diff (i := j) (j := i) hx]
  ring
end
end
end WeightedGradientTestDerivative
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
private lemma FunctionalInequalities.Analysis.continuous_coord {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (FunctionalInequalities.Analysis.coord f i) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
private lemma FunctionalInequalities.Analysis.integrable_energy {n : ℕ}
    {u F a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (ha : ∀ i, Continuous (FunctionalInequalities.Analysis.coord a i))
    (hf : ∀ j, Continuous (FunctionalInequalities.Analysis.coord f j))
    (hc : ∀ i j, HasCompactSupport
      (fun x => FunctionalInequalities.Analysis.coord a i x * FunctionalInequalities.Analysis.coord f j x * Real.exp (-u x))) :
    Integrable (FunctionalInequalities.Analysis.energyDensity u a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hi (i j : Fin n) :
      Integrable
        (fun x => (hessianMatrix u x)⁻¹ i j *
          (FunctionalInequalities.Analysis.coord a i x * FunctionalInequalities.Analysis.coord f j x * Real.exp (-u x)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hcont : Continuous
        (fun x => FunctionalInequalities.Analysis.coord a i x * FunctionalInequalities.Analysis.coord f j x * Real.exp (-u x)) :=
      ((ha i).mul (hf j)).mul
        (Real.continuous_exp.comp hu.continuous.neg)
    obtain ⟨C, hC⟩ := (hc i j).exists_bound_of_continuous hcont
    exact integrable_inv_hessianMatrix_mul_of_bounded_compact_408915f
      hG hF hdet hcont.measurable (hc i j) hC i j
  have hs := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
  have he :
      (fun x => ∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
        (FunctionalInequalities.Analysis.coord a i x * FunctionalInequalities.Analysis.coord f j x * Real.exp (-u x))) =
        FunctionalInequalities.Analysis.energyDensity u a f := by
    funext x
    simp only [FunctionalInequalities.Analysis.energyDensity, Finset.sum_mul, mul_assoc]
  rw [he] at hs
  exact hs
end
end
end GeneratorIdentities
section C1GeneratorTestReuse
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- C1 compact multiplier version of the closed weak generator identity.
Weak-source support for Letwin A.4; no new regularity hypothesis on u. -/
theorem solution {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (FunctionalInequalities.Probability.Stein.hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ x, η x * (((FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ * FunctionalInequalities.Probability.Stein.hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (FunctionalInequalities.Probability.Stein.hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hη1 : ContDiff ℝ 1 η := hη
  have hE : Integrable (FunctionalInequalities.Analysis.energyDensity u η w)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_energy hu hG hF.continuous hdet
      (continuous_coord hη1) (continuous_coord hw)
    intro i j
    exact
      ((hηc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).mul_right :
        HasCompactSupport (fun x => FunctionalInequalities.Analysis.coord η i x * FunctionalInequalities.Analysis.coord w j x)).mul_right
  exact FunctionalInequalities.Analysis.assemble_generator_408915f hu hG hV hF hdet
    (fun i => exists_lipschitz_compact_exp_gradient_test hu hη1 hηc hGw i)
    (fun i => ae_fderiv_exp_gradient_test hu hη1 hGw i) hE
