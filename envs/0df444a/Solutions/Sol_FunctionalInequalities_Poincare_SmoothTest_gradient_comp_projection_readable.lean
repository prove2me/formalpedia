-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.gradient_comp_projection_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:56.055325+00:00
-- url     : https://prove2.me/submissions/ef3e5fb1-45a0-487f-84d9-88216ed4bda2

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Transport

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
section CoordinateLift
variable (q : E →L[ℝ] F)
/-- The gradient chain rule uses the Hilbert adjoint.
Source: local helper from `HasFDerivAt.comp`, `toDual_gradient`, and
`ContinuousLinearMap.adjoint_inner_left` in Mathlib. -/
theorem solution {f : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (q x)) :
    gradient (f ∘ q) x = q.adjoint (gradient f (q x)) := by
  have hcomp : HasFDerivAt (f ∘ q) ((fderiv ℝ f (q x)).comp q) x :=
    hf.hasFDerivAt.comp x q.hasFDerivAt
  have hkey : (fderiv ℝ f (q x)).comp q
      = InnerProductSpace.toDual ℝ E (q.adjoint (gradient f (q x))) := by
    ext h
    rw [ContinuousLinearMap.comp_apply, ← toDual_gradient,
      InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDual_apply_apply,
      ContinuousLinearMap.adjoint_inner_left]
  have hgrad : HasGradientAt (f ∘ q) (q.adjoint (gradient f (q x))) x := by
    rw [hasGradientAt_iff_hasFDerivAt, ← hkey]
    exact hcomp
  exact hgrad.gradient
