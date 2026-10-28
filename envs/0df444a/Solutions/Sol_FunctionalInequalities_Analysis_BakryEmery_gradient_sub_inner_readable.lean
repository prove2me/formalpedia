-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.gradient_sub_inner_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:18.59799+00:00
-- url     : https://prove2.me/submissions/1aa9612c-22f0-4aa9-9f9b-93ab2f20aefe

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The gradient of `V - ⟪z, ·⟫` is `∇V - z`. -/
theorem solution {V : E → ℝ} (z x : E) (hV : DifferentiableAt ℝ V x) :
    gradient (fun y => V y - ⟪z, y⟫) x = gradient V x - z := by
    have hinner' :
        HasFDerivAt (fun y : E => ⟪z, y⟫)
          (InnerProductSpace.toDual ℝ E z) x := by
      change HasFDerivAt (fun y : E => innerSL ℝ z y) (innerSL ℝ z) x
      exact (innerSL ℝ z).hasFDerivAt
    have hsub' :
        HasFDerivAt (fun y : E => V y - ⟪z, y⟫)
          (InnerProductSpace.toDual ℝ E (gradient V x) -
            InnerProductSpace.toDual ℝ E z) x :=
      ((hasGradientAt_iff_hasFDerivAt).1 hV.hasGradientAt).sub hinner'
    have hsubgrad :
        HasGradientAt (fun y : E => V y - ⟪z, y⟫)
          (gradient V x - z) x := by
      apply (hasGradientAt_iff_hasFDerivAt).2
      simpa [Pi.sub_apply] using hsub'
    exact hsubgrad.gradient
