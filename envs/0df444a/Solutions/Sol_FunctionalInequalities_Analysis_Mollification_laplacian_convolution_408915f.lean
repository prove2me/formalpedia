-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Mollification.laplacian_convolution_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:56:28.651342+00:00
-- url     : https://prove2.me/submissions/53e745f6-6933-492e-a7b6-db710f78b363

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : Measure V} [m.IsAddHaarMeasure]
section Derivative
variable (φ : ContDiffBump (0 : V))
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.Mollification in
/-- The mollifier commutes with the Laplacian on smooth compactly supported functions:
`Δ(ρ ⋆ g) = ρ ⋆ Δg`. -/
theorem solution {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : V) :
    Laplacian.laplacian (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] Laplacian.laplacian g) x := by
  have hρ : LocallyIntegrable (φ.normed m) m := φ.integrable_normed.locallyIntegrable
  have hg1 : ContDiff ℝ 1 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgD : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)
  have hgc1 : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  have hconv : ContDiff ℝ ∞ (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) :=
    HasCompactSupport.contDiff_convolution_left _ (φ.hasCompactSupport_normed (μ := m))
      φ.contDiff_normed (hg1.continuous.locallyIntegrable)
  have hdiffx : DifferentiableAt ℝ (fderiv ℝ (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g)) x :=
    (hconv.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiable one_ne_zero x
  -- the directional derivative of the mollification is the mollification of the directional
  -- derivative
  have hdir : ∀ v, (fun y => fderiv ℝ (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) y v) =
      φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun a => fderiv ℝ g a v := by
    intro v
    funext y
    rw [(HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hgc hρ hg1
      y).fderiv, convolution_precompR_apply _ hρ hgc1 hgD.continuous]
  -- the second derivative
  have hsecond : ∀ v w, fderiv ℝ (fderiv ℝ (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g)) x v w
      = (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun a => fderiv ℝ (fderiv ℝ g) a v w) x := by
    intro v w
    rw [← FunctionalInequalities.Analysis.BakryEmery.fderiv_fderiv_apply hdiffx v w, hdir w]
    have hw1 : ContDiff ℝ 1 fun a => fderiv ℝ g a w := hgD.clm_apply contDiff_const
    have hwc : HasCompactSupport fun a => fderiv ℝ g a w := hgc.fderiv_apply ℝ w
    rw [(HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hwc hρ hw1
      x).fderiv, convolution_precompR_apply _ hρ (hwc.fderiv ℝ) (hw1.continuous_fderiv one_ne_zero)]
    simp only [convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [FunctionalInequalities.Analysis.BakryEmery.fderiv_fderiv_apply (hgD.differentiable one_ne_zero _) v w]
  have hg2c : Continuous (fderiv ℝ (fderiv ℝ g)) := hgD.continuous_fderiv one_ne_zero
  have hint : ∀ i, Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ (φ.normed m t))
      (fderiv ℝ (fderiv ℝ g) (x - t) (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V i))) m :=
    fun i =>
    HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (φ.hasCompactSupport_normed (μ := m)) φ.continuous_normed
      (((hg2c.clm_apply continuous_const).clm_apply continuous_const).locallyIntegrable) x
  rw [FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_fderiv]
  simp only [hsecond, convolution_def]
  rw [← integral_finsetSum _ fun i _ => hint i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_fderiv,
    Finset.mul_sum]
