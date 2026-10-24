-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.gradient_comp_projection_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:04:00.613023+00:00
-- url     : https://prove2.me/submissions/d82c3c8e-f784-4d16-ad4b-cf34b57523da

import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
section CoordinateLift
variable (q : E →L[ℝ] F)
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities.Poincare.SmoothTest in
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
