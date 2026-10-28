-- Prove2me | solution 1 for FunctionalInequalities.Analysis.inner_iteratedFDeriv_gradient_apply_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:12.820552+00:00
-- url     : https://prove2.me/submissions/137e9070-9a49-4d41-9cb3-0a4f8f6b5677

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_GradientJet

noncomputable section
open scoped RealInnerProductSpace ContDiff
section GradientJet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
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
