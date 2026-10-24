-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_inner_sq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:23:52.320496+00:00
-- url     : https://prove2.me/submissions/4922bf76-f5db-46a4-869f-f8ab5952a2b2

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_laplace_408915f

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
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.hasFDerivAt_exp_norm_sq_div {s : ℝ} (hs : 0 < s) (z : E) :
    HasFDerivAt (fun w : E => Real.exp (‖w‖ ^ 2 / (4 * s)))
      ((Real.exp (‖z‖ ^ 2 / (4 * s)) / (2 * s)) • innerSL ℝ z) z := by
  have hn : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hq : HasFDerivAt (fun w : E => ‖w‖ ^ 2 / (4 * s))
      ((4 * s)⁻¹ • (2 • innerSL ℝ z)) z := by
    convert! hn.const_mul (4 * s)⁻¹ using 1
    funext w
    simp only [div_eq_mul_inv]
    ring
  have h := hq.exp
  convert h using 1
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp [hs.ne']
  ring
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing in
omit [CompleteSpace E] in
/-- `∫ ⟪v,y⟫² dγ_s = ‖v‖²/(2s)`. -/
theorem solution {s : ℝ} (hs : 0 < s) (v : E) :
    (∫ y : E, ⟪v, y⟫ ^ 2 ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) = ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s) := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_probability hs
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s) := by
    simpa only [one_mul] using FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_exp_norm_integrable_408915f (E := E) hs
  let F : E → ℝ := fun z => Real.exp (‖z‖ ^ 2 / (4 * s))
  have hF : ContDiff ℝ 2 F := ((contDiff_norm_sq ℝ).div_const (4 * s)).exp
  have hm := FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_laplace_zero (FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw (V := E) s)
    (by norm_num : (0 : ℝ) < 1) he 2 ![v, v]
  have hfunL : (fun z : E => ∫ y, Real.exp ⟪z, y⟫ ∂(FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw s)) = F :=
    funext fun z => FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_laplace_408915f hs z
  rw [hfunL] at hm
  have hprod : (fun y : E => ∏ j : Fin 2, ⟪y, (![v, v] : Fin 2 → E) j⟫) =
      fun y => ⟪v, y⟫ ^ 2 := by
    funext y
    simp [Fin.prod_univ_two, pow_two, real_inner_comm]
  rw [hprod, ← bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply hF] at hm
  have hfun : (fun z : E => fderiv ℝ F z v) =
      fun z => (F z / (2 * s)) * ⟪v, z⟫ := by
    funext z
    rw [(hasFDerivAt_exp_norm_sq_div hs z).fderiv]
    simp [F, innerSL_apply_apply, real_inner_comm]
  have hzero : HasFDerivAt F (0 : E →L[ℝ] ℝ) 0 := by
    simpa only [F, innerSL, map_zero, smul_zero] using hasFDerivAt_exp_norm_sq_div hs (0 : E)
  have hscaled : HasFDerivAt (fun z => F z / (2 * s)) (0 : E →L[ℝ] ℝ) 0 := by
    convert! hzero.const_mul (2 * s)⁻¹ using 1
    · funext z
      simp only [div_eq_mul_inv]
      ring
    · simp
  have hd : HasFDerivAt (fun z => F z / (2 * s) * ⟪v, z⟫)
      ((1 / (2 * s)) • innerSL ℝ v) 0 := by
    simpa only [Pi.mul_def, coe_innerSL_apply, F, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, Real.exp_zero, inner_zero_right, zero_smul, add_zero] using
      hscaled.mul ((innerSL ℝ v).hasFDerivAt (x := (0 : E)))

  rw [hfun, hd.fderiv] at hm
  simpa only [F, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.exp_zero,
    inner_zero_right, innerSL_apply_apply, add_apply,
    smul_apply, smul_eq_mul, zero_apply,
    mul_zero, zero_smul, zero_add, add_zero, real_inner_self_eq_norm_sq,
    one_div, one_mul, div_eq_mul_inv, mul_comm] using hm.symm
