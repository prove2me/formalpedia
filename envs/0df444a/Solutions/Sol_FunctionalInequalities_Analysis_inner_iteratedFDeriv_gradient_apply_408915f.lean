-- Prove2me | solution 1 for FunctionalInequalities.Analysis.inner_iteratedFDeriv_gradient_apply_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:43:20.629006+00:00
-- url     : https://prove2.me/submissions/ea70ce8b-0437-4ef5-b0a7-be3dfbaa0fe2

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section GradientJet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Jets of the gradient pair with the next derivative**:
`⟪Dʳ(∇f)(x)[h], w⟫ = Dʳ⁺¹f(x)[h, w]`, the new direction `w` in the last slot. -/
theorem solution {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℕ) (x : E)
    (h : Fin r → E) (w : E) :
    ⟪iteratedFDeriv ℝ r (gradient f) x h, w⟫ = iteratedFDeriv ℝ (r + 1) f x (Fin.snoc h w) := by
    have _hf : ContDiff ℝ ∞ f := hf
    let L : (E →L[ℝ] ℝ) ≃L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
    have hpoint :
        iteratedFDeriv ℝ r (gradient f) x h =
          L (iteratedFDeriv ℝ r (fderiv ℝ f) x h) := by
      have hc :=
        L.iteratedFDeriv_comp_left
          (f := fderiv ℝ f) (x := x) (i := r)
      have hc' := congrArg (fun q => q h) hc
      change
        iteratedFDeriv ℝ r
            (fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) x h =
          (InnerProductSpace.toDual ℝ E).symm
            (iteratedFDeriv ℝ r (fderiv ℝ f) x h)
      simpa [L, Function.comp_def] using hc'
    calc
      ⟪iteratedFDeriv ℝ r (gradient f) x h, w⟫ =
          ⟪L (iteratedFDeriv ℝ r (fderiv ℝ f) x h), w⟫ := by
            rw [hpoint]
      _ = iteratedFDeriv ℝ (r + 1) f x (Fin.snoc h w) := by
        rw [iteratedFDeriv_succ_apply_right]
        simp [L]
