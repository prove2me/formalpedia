-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasFDerivAt_convolution_normed_of_lipschitz_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:03.162736+00:00
-- url     : https://prove2.me/submissions/5d858cf8-e5f6-4bbc-a1ff-879dcef07fd8

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic
import Theorems.Thm_FunctionalInequalities_Analysis_integral_fderiv_kernel_eq_readable

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section LipschitzConvolution
open MeasureTheory
open scoped Convolution
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
/-- **Derivative of the mollification of a Lipschitz map** (weak Letwin route, support for the
mollification identities): for a Lipschitz map `F : E → E` and a bump `φ`, the convolution
`φ.normed ⋆ F` is differentiable with derivative `φ.normed ⋆ DF`, where `DF = fderiv ℝ F` is the
almost-everywhere (Rademacher) derivative of `F` (a bounded measurable map). -/
theorem solution
    {F : E → E} {G : NNReal} (hF : LipschitzWith G F) (φ : ContDiffBump (0 : E)) (x : E) :
    HasFDerivAt (φ.normed (volume : Measure E) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] F)
      ((φ.normed (volume : Measure E) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        fderiv ℝ F) x) x := by
  let k := φ.normed (volume : Measure E)
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  let P := ContinuousLinearMap.precompL E L
  have hk : ContDiff ℝ 1 k := φ.contDiff_normed
  have hc : HasCompactSupport k := φ.hasCompactSupport_normed
  have hDF : LocallyIntegrable (fderiv ℝ F) (volume : Measure E) :=
    (memLp_top_of_bound (measurable_fderiv ℝ F).aestronglyMeasurable
      (G : ℝ)
      (Filter.Eventually.of_forall
        (fun _ => norm_fderiv_le_of_lipschitz ℝ hF))).locallyIntegrable le_top
  have hFloc : LocallyIntegrable F (volume : Measure E) :=
    hF.continuous.locallyIntegrable
  have hi :=
    (hc.fderiv ℝ).convolutionExists_left P
      (hk.continuous_fderiv (by decide)) hFloc x
  have hj :=
    hc.convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E))
      hk.continuous hDF x
  change Integrable (fun t => k t • fderiv ℝ F (x - t))
    (volume : Measure E) at hj
  apply (hc.hasFDerivAt_convolution_left L hk hFloc x).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro w
  let ℓ : E →L[ℝ] ℝ := innerSL ℝ w
  let Q : (E →L[ℝ] E) →L[ℝ] ℝ :=
    ℓ.comp (ContinuousLinearMap.apply ℝ E v)
  change Q (∫ t, P (fderiv ℝ k t) (F (x - t))) =
    Q (∫ t, k t • fderiv ℝ F (x - t))
  rw [← Q.integral_comp_comm hi, ← Q.integral_comp_comm hj]
  simpa only [Q, P, L, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.lsmul_apply, map_smul, smul_eq_mul] using
    FunctionalInequalities.Analysis.integral_fderiv_kernel_eq_readable hF k hk hc x v ℓ
