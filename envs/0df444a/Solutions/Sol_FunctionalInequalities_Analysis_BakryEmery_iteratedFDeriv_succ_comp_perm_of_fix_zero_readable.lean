-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_succ_comp_perm_of_fix_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:51.506519+00:00
-- url     : https://prove2.me/submissions/4855e772-d7d8-4782-a448-5af2ce6e3358

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IteratedDerivative

noncomputable section
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Symmetry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- If `∇ⁿf` is symmetric at every point, `∇ⁿ⁺¹f(x)` is invariant under permutations fixing the
first (differentiation) index. -/
theorem solution {f : E → F} (hf : ContDiff ℝ ∞ f) {n : ℕ}
    (ih : ∀ (y : E) (w : Fin n → E) (τ : Equiv.Perm (Fin n)),
      iteratedFDeriv ℝ n f y (w ∘ τ) = iteratedFDeriv ℝ n f y w)
    (x : E) (v : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ 0 = 0) :
    iteratedFDeriv ℝ (n + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (n + 1) f x v := by
    have hne : ∀ i : Fin n, σ i.succ ≠ 0 := by
      intro i hi
      have hs : σ i.succ = σ 0 := by
        rw [hi, hσ]
      exact Fin.succ_ne_zero i (σ.injective hs)

    let p : Fin n → Fin n := fun i => Fin.pred (σ i.succ) (hne i)

    have hp : Function.Injective p := by
      intro i j hij
      apply Fin.succ_injective
      have hs : (p i).succ = (p j).succ := congrArg Fin.succ hij
      simpa [p] using hs

    have hp' : Function.Surjective p :=
      (Finite.injective_iff_surjective).mp hp

    let τ : Equiv.Perm (Fin n) :=
      Equiv.ofBijective p ⟨hp, hp'⟩

    have hτ : ∀ i : Fin n, (τ i).succ = σ i.succ := by
      intro i
      change (p i).succ = σ i.succ
      simp [p]

    have htail : Fin.tail (v ∘ σ) = (Fin.tail v) ∘ τ := by
      funext i
      simp only [Function.comp_apply, Fin.tail]
      rw [hτ i]

    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
      ContDiff.differentiable_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top n) hf

    have hfun :
        (fun y => iteratedFDeriv ℝ n f y ((Fin.tail v) ∘ τ)) =
          (fun y => iteratedFDeriv ℝ n f y (Fin.tail v)) := by
      funext y
      exact ih y (Fin.tail v) τ

    calc
      iteratedFDeriv ℝ (n + 1) f x (v ∘ σ) =
          fderiv ℝ (iteratedFDeriv ℝ n f) x
            ((v ∘ σ) 0) (Fin.tail (v ∘ σ)) := by
        rw [iteratedFDeriv_succ_apply_left]
      _ = fderiv ℝ (iteratedFDeriv ℝ n f) x
            (v 0) ((Fin.tail v) ∘ τ) := by
        simp only [Function.comp_apply, hσ]
        rw [htail]
      _ = fderiv ℝ
            (fun y => iteratedFDeriv ℝ n f y ((Fin.tail v) ∘ τ)) x (v 0) := by
        exact
          (fderiv_continuousMultilinear_apply_const_apply
            (hdiff x) ((Fin.tail v) ∘ τ) (v 0)).symm
      _ = fderiv ℝ
            (fun y => iteratedFDeriv ℝ n f y (Fin.tail v)) x (v 0) := by
        rw [hfun]
      _ = fderiv ℝ (iteratedFDeriv ℝ n f) x (v 0) (Fin.tail v) := by
        exact
          fderiv_continuousMultilinear_apply_const_apply
            (hdiff x) (Fin.tail v) (v 0)
      _ = iteratedFDeriv ℝ (n + 1) f x v := by
        rw [iteratedFDeriv_succ_apply_left]
