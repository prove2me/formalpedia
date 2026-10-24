-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_directional_identity_of_bounded_lipschitz_test_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:28:43.199693+00:00
-- url     : https://prove2.me/submissions/35805da1-6b94-43f1-b6fa-110645b6fe82

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_contDiff_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_integral_eq_zero_of_integrable_weak_derivative_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_408915f

section
open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
section
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] in
/-- The Gaussian noise law `γ_s` is the tilt of Lebesgue measure by `e^{-s‖y‖²}`. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_eq_tilted {s : ℝ} (hs : 0 < s) :
    gaussianLaw (V := E) s = (volume : Measure E).tilted (fun y => -s * ‖y‖ ^ 2) := by
  have hmass : (∫ y : E, Real.exp (-s * ‖y‖ ^ 2)) = mass (V := E) s := integral_kernel hs
  unfold gaussianLaw Measure.tilted normalizedKernel kernel
  rw [hmass]
omit [CompleteSpace E] in
/-- `γ_s` has a finite second moment. -/
theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two {s : ℝ} (hs : 0 < s) : MemLp id 2 (gaussianLaw (V := E) s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable_408915f (E := E) hs
  exact (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    (Probability.integrable_norm_pow_of_integrable_exp_norm (by norm_num : (0 : ℝ) < 1) he 2)
end
end
end
end
section GaussianDirectionalIdentity
open MeasureTheory Filter
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
section
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing in
set_option maxHeartbeats 800000 in
/-- Gaussian integration by parts for C1 bounded globally Lipschitz tests: under `gaussianLaw s` (`s > 0`, all dimensions),
`∫ ⟪x, v⟫ f = (2 s)⁻¹ ∫ D_v f`, with both integrands integrable. -/
theorem solution {n : ℕ}
    {s : ℝ} (hs : 0 < s) {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith L f) (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => ⟪x, v⟫ * f x) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) ∧
    Integrable (fun x => fderiv ℝ f x v) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) ∧
    (∫ x, ⟪x, v⟫ * f x ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) =
      (2 * s)⁻¹ * ∫ x, fderiv ℝ f x v ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) := by
  let E := EuclideanSpace ℝ (Fin n)
  let w : E → ℝ := fun x => Real.exp (-s * ‖x‖ ^ 2)
  let mu : Measure E := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s
  let : IsProbabilityMeasure mu := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have hexp : Integrable (fun x : E => Real.exp (-s * ‖x‖ ^ 2)) volume := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_kernel hs
  have hF : Integrable f mu :=
    (integrable_const C).mono' hf.continuous.aestronglyMeasurable (ae_of_all _ hbound)
  have hX : Integrable (fun x : E => ⟪x, v⟫) mu :=
    ((FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_memLp_two hs).inner_const (𝕜 := ℝ) v).integrable one_le_two
  have hXF : Integrable (fun x : E => ⟪x, v⟫ * f x) mu :=
    hX.mul_bdd hf.continuous.aestronglyMeasurable (ae_of_all _ hbound)
  have hdfmeas : Measurable (fun x : E => fderiv ℝ f x v) :=
    (continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ f)
  have hDF : Integrable (fun x : E => fderiv ℝ f x v) mu := by
    apply (integrable_const ((L : ℝ) * ‖v‖)).mono' hdfmeas.aestronglyMeasurable
    exact ae_of_all _ fun x => ((fderiv ℝ f x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg v))
  have raw (k : E → ℝ) (hk : Integrable k mu) : Integrable (fun x => w x * k x) volume := by
    have hkt : Integrable k ((volume : Measure E).tilted (fun x => -s * ‖x‖ ^ 2)) := by
      rwa [← FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_eq_tilted hs]
    simpa only [w, smul_eq_mul] using (integrable_tilted_iff hexp k).mp hkt
  have hRawF := raw f hF
  have hRawXF := raw (fun x => ⟪x, v⟫ * f x) hXF
  have hRawDF := raw (fun x => fderiv ℝ f x v) hDF
  have hw : ContDiff ℝ 1 w := by
    have hn : ContDiff ℝ 1 (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
    exact ((contDiff_const : ContDiff ℝ 1 (fun _ : E => -s)).mul hn).exp
  have hd (x : E) : fderiv ℝ (fun y => w y * f y) x v =
      w x * fderiv ℝ f x v - (2 * s) * (w x * (⟪x, v⟫ * f x)) := by
    have hwx : HasFDerivAt w (w x • ((-s) • (2 • innerSL ℝ x))) x :=
      ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-s)).exp
    change fderiv ℝ (w * f) x v = _
    rw [(hwx.mul ((hf.differentiable one_ne_zero x).hasFDerivAt)).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply]
    ring
  have hRawD : Integrable (fun x => fderiv ℝ (fun y => w y * f y) x v) volume := by
    apply (hRawDF.sub (hRawXF.const_mul (2 * s))).congr
    filter_upwards [] with x
    exact (hd x).symm
  have hz := FunctionalInequalities.Analysis.integral_eq_zero_of_integrable_weak_derivative_408915f
    (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff_408915f (hw.mul hf) v) hRawF hRawD
  have hRawEq : (∫ x, w x * fderiv ℝ f x v ∂volume) =
      (2 * s) * ∫ x, w x * (⟪x, v⟫ * f x) ∂volume := by
    have heq : (∫ x, fderiv ℝ (fun y => w y * f y) x v ∂volume) =
        (∫ x, w x * fderiv ℝ f x v ∂volume) -
        (2 * s) * ∫ x, w x * (⟪x, v⟫ * f x) ∂volume := by
      calc
        _ = ∫ x, w x * fderiv ℝ f x v - (2 * s) * (w x * (⟪x, v⟫ * f x)) ∂volume :=
          integral_congr_ae (ae_of_all _ hd)
        _ = _ := by rw [integral_sub hRawDF (hRawXF.const_mul (2 * s)), integral_const_mul]
    linarith
  have htilt (k : E → ℝ) : (∫ x, k x ∂mu) =
      (∫ x, w x * k x ∂volume) / (∫ x, w x ∂volume) := by
    dsimp only [mu]
    rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_eq_tilted hs, integral_tilted]
    change (∫ x, (w x / (∫ y, w y ∂volume)) * k x ∂volume) = _
    simp_rw [div_mul_eq_mul_div]
    exact integral_div _ _
  refine ⟨hXF, hDF, ?_⟩
  change (∫ x, ⟪x, v⟫ * f x ∂mu) = (2 * s)⁻¹ * ∫ x, fderiv ℝ f x v ∂mu
  rw [htilt, htilt, hRawEq, mul_div_assoc, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hs)), one_mul]
