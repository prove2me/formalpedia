-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Mollification.laplacian_convolution_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:55.386405+00:00
-- url     : https://prove2.me/submissions/eb7581ce-bbb1-4969-816e-46d5dda0ed8d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
section Derivative
variable (φ : ContDiffBump (0 : V))
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
