-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integrable_gradient_expTilt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:26.966606+00:00
-- url     : https://prove2.me/submissions/28ad0378-e5b9-4275-a9a4-6c619822e2fa

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
omit [m.IsAddHaarMeasure] in
/-- The gradient of a compactly supported `C²` function is integrable for every exponential tilt of
`m.tilted (-V)`. -/
theorem solution {V f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (z : E) : Integrable (gradient f) (FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z) := by
    have hfd : Continuous (fderiv ℝ f) :=
      hf.continuous_fderiv (by norm_num)
    have hgrad : Continuous (gradient f) := by
      change Continuous
        (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
      exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp hfd
    have hfd_cs : HasCompactSupport (fderiv ℝ f) :=
      hfc.fderiv (𝕜 := ℝ)
    have hgrad_cs : HasCompactSupport (gradient f) := by
      change HasCompactSupport
        (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
      exact hfd_cs.comp_left (InnerProductSpace.toDual ℝ E).symm.map_zero
    unfold FunctionalInequalities.Analysis.BakryEmery.expTilt
    exact hgrad.integrable_of_hasCompactSupport hgrad_cs
